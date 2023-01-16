// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

type UM256 is uint256;

using {
    sum,
    header,
    shape,
    dim0,
    dim1,
    length,
    sizeBytes,
    ref,
    reshape,
    _bytes,
    copy,
    at,
    atIndex,
    set,
    setIndex,
    fill_,
    add,
    addScalarUnchecked,
    mulScalarUnchecked,
    add,
    dot,
    dotTransposed,
    eq,
    eqScalar,
    sum
} for UM256 global;

error UM256_TooLarge();
error UM256_InvalidRange();
error UM256_IndexOutOfBounds();
error UM256_InvalidDimensions();
error UM256_IncompatibleDimensions();

uint256 constant MAX_08_BITS = 0xff;
uint256 constant MAX_16_BITS = 0xffff;
uint256 constant MAX_24_BITS = 0xffffff;
uint256 constant MAX_32_BITS = 0xffffffff;
uint256 constant MAX_64_BITS = 0xffffffffffffffff;

/* ------------- malloc ------------- */

function malloc(uint256 size) pure returns (uint256 ptr) {
    assembly {
        // Load free memory pointer.
        ptr := mload(0x40)

        // Update free memory pointer.
        mstore(0x40, add(ptr, size))
    }
}

function mcopy(uint256 fromPtr, uint256 toPtr, uint256 size) view {
    assembly {
        // Use `address(4)` precompile to copy memory data.
        pop(staticcall(gas(), 4, fromPtr, size, toPtr, size))
    }
}

/* ------------- header ------------- */

struct UM256HeaderStruct {
    uint24 n; // first dimension `dim0`
    uint24 m; // second dimension `dim1`
    uint64 dataPtr; // pointer to matrix memory data
    uint24 startx; // start offset of `dim0`
    uint24 starty; // start offset of `dim1`
    uint24 endx; // end offset of `dim0`
    uint24 endy; // end offset of `dim1`
    uint8 stridex; // stride of `dim0`
    uint8 stridey; // stride of `dim1`
    bool T; // transposed
}

function UM256Header(uint256 ptr, uint256 n, uint256 m) pure returns (UM256 A) {
    A = UM256.wrap(
        ptr << 48 // data location
            | m << 24 | n // shape
    );

    if ((n | m | (ptr >> 40)) > MAX_24_BITS) revert UM256_TooLarge();
}

function header(UM256 A) pure returns (uint256 n, uint256 m, uint256 ptr) {
    n = (UM256.unwrap(A)) & MAX_24_BITS;
    m = (UM256.unwrap(A) >> 24) & MAX_24_BITS;
    ptr = (UM256.unwrap(A) >> 48) & MAX_64_BITS;
}

function shape(UM256 A) pure returns (uint256 n, uint256 m) {
    n = (UM256.unwrap(A)) & MAX_24_BITS;
    m = (UM256.unwrap(A) >> 24) & MAX_24_BITS;
}

function dim0(UM256 A) pure returns (uint256 n) {
    n = (UM256.unwrap(A)) & MAX_24_BITS;
}

function dim1(UM256 A) pure returns (uint256 m) {
    m = (UM256.unwrap(A) >> 24) & MAX_24_BITS;
}

function length(UM256 A) pure returns (uint256 len) {
    unchecked {
        uint256 n = (UM256.unwrap(A)) & MAX_24_BITS;
        uint256 m = (UM256.unwrap(A) >> 24) & MAX_24_BITS;

        len = n * m;
    }
}

function sizeBytes(UM256 A) pure returns (uint256 size) {
    unchecked {
        uint256 n = (UM256.unwrap(A)) & MAX_24_BITS;
        uint256 m = (UM256.unwrap(A) >> 24) & MAX_24_BITS;

        size = n * m * 32;
    }
}

function ref(UM256 A) pure returns (uint256 ptr) {
    ptr = (UM256.unwrap(A) >> 48) & MAX_64_BITS;
}

/* ------------- constructors ------------- */

function mallocUM256(uint256 n, uint256 m) pure returns (UM256 A) {
    unchecked {
        // Memory size in bytes.
        uint256 size = n * m * 32;
        // Allocate memory for matrix.
        // Add 32 bytes to store the byte size.
        uint256 ptr = malloc(32 + size);

        assembly {
            mstore(ptr, size) // Store the bytes size.
        }

        // Generate metadata header, skip the 32 bytes length.
        // This is only for convenience when converting to `bytes`.
        A = UM256Header(ptr + 32, n, m);
    }
}

function zeros(uint256 n, uint256 m) pure returns (UM256 C) {
    C = mallocUM256(n, m); // Allocate memory for matrix.

    fill_(C, 0); // Fill matrix with `0`s.
}

function ones(uint256 n, uint256 m) pure returns (UM256 C) {
    C = mallocUM256(n, m); // Allocate memory for matrix.

    fill_(C, 1); // Fill matrix with `1`s.
}

function eye(uint256 n, uint256 m) pure returns (UM256 C) {
    unchecked {
        // Only allowing square dimensions.
        if (n != m) revert UM256_InvalidDimensions();

        // Allocate memory for matrix.
        C = mallocUM256(n, m);

        // Fill matrix with `0`.
        fill_(C, 0);

        // Obtain a pointer to matrix data location.
        uint256 ptr = ref(C);
        // Spacing in memory between the elements on the diagonal.
        uint256 diagSpace = 32 + n * 32;
        // Loop over n diagonal elements.
        uint256 end = ptr + n * diagSpace;

        while (ptr != end) {
            assembly {
                mstore(ptr, 1) // Store `1` at current pointer location.
            }

            ptr = ptr + diagSpace; // Advance pointer to the next slot in the diagonal.
        }
    }
}

function range(uint256 start, uint256 end) pure returns (UM256 A) {
    unchecked {
        // `start <= end` must hold.
        if (start > end) revert UM256_InvalidRange();

        uint256 numEl = end - start;

        // Allocate memory for matrix.
        A = mallocUM256(1, numEl);

        // Obtain a pointer to matrix data location.
        uint256 ptr = ref(A);

        uint256 a = start;
        uint256 aEnd = a + numEl;

        while (a != aEnd) {
            assembly {
                mstore(ptr, a) // Store `a` at current pointer location.
            }

            ptr = ptr + 32; // Advance pointer to the next slot.
            a = a + 1;
        }
    }
}

function range(uint256 end) pure returns (UM256 A) {
    return range(0, end);
}

function reshape(UM256 A, uint256 nNew, uint256 mNew) pure returns (UM256 out) {
    unchecked {
        (uint256 n, uint256 m, uint256 data) = header(A);

        if (n * m != nNew * mNew) revert UM256_InvalidDimensions();

        out = UM256Header(data, nNew, mNew);
    }
}

/* ------------- indexing ------------- */

function atIndex(UM256 A, uint256 index) pure returns (uint256 a) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        if (index >= n * m) revert UM256_IndexOutOfBounds();

        ptr = ptr + 32 * index;

        assembly {
            a := mload(ptr)
        }
    }
}

function setIndex(UM256 A, uint256 index, uint256 value) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        if (index >= n * m) revert UM256_IndexOutOfBounds();

        ptr = ptr + 32 * index;

        assembly {
            mstore(ptr, value)
        }
    }
}

function at(UM256 A, uint256 i, uint256 j) pure returns (uint256 a) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        if (i >= n || j >= m) revert UM256_IndexOutOfBounds();

        ptr = ptr + 32 * (i * m + j);

        assembly {
            a := mload(ptr)
        }
    }
}

function set(UM256 A, uint256 i, uint256 j, uint256 value) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        if (i >= n || j >= m) revert UM256_IndexOutOfBounds();

        ptr = ptr + 32 * (i * m + j);

        assembly {
            mstore(ptr, value)
        }
    }
}

/* ------------- Mat x Mat operators ------------- */

function add(UM256 A, UM256 B) pure returns (UM256 C) {
    unchecked {
        (uint256 nA, uint256 mA, uint256 ptrA) = header(A);
        (uint256 nB, uint256 mB, uint256 ptrB) = header(B);

        if (nA != nB || mA != mB) revert UM256_IncompatibleDimensions();

        C = mallocUM256(nA, mA);

        // Loop over all `n * m` elements of 32 bytes size.
        uint256 endA = ptrA + nA * mA * 32;
        uint256 ptrC = ref(C);

        // Loop over 32 byte words.
        while (ptrA != endA) {
            assembly {
                let a := mload(ptrA)
                let b := mload(ptrB)
                let c := add(a, b)

                mstore(ptrC, c) // Store result in `C`.
            }

            // Advance pointers to the next slot.
            ptrA = ptrA + 32;
            ptrB = ptrB + 32;
            ptrC = ptrC + 32;
        }
    }
}

/// Perform the matrix multiplication given by:
/// `C_ij = A_ik B_kj`
///
/// Given `i`, `j`, `k`, the offsets
/// of the elements in `A`, `B` to be summed are:
/// `ptrA = 32 * (k + i * mA)`
/// `ptrB = 32 * (j + k * mb)`
function dot(UM256 A, UM256 B) pure returns (UM256 C) {
    unchecked {
        (uint256 nA, uint256 mA, uint256 dataPtrA) = header(A);
        (uint256 nB, uint256 mB, uint256 dataPtrB) = header(B);

        if (mA != nB) revert UM256_IncompatibleDimensions();

        C = mallocUM256(nA, mB);

        uint256 ptrCij = ref(C);

        uint256 ptrARowSize = 32 * mA;
        uint256 ptrBRowSize = 32 * mB;

        uint256 ptrAiEnd = dataPtrA + 32 * nA * mA;
        uint256 ptrAi = dataPtrA; // Updates by row size of `A` in i-loop.

        uint256 ptrBjEnd = dataPtrB + ptrBRowSize;
        uint256 ptrBj;

        // Loop over `C`s `i` indices.
        while (ptrAi != ptrAiEnd) {
            // i-loop start.

            ptrBj = dataPtrB;

            while (ptrBj != ptrBjEnd) {
                // j-loop start.

                uint256 ptrBkj = ptrBj;
                uint256 ptrAik = ptrAi;
                uint256 ptrAikEnd = ptrAi + ptrARowSize;

                // Perform the dot product on the current
                // row vector of `A` and the column vector of `B`.
                // Store the result in `c`.
                uint256 c;

                // Loop over 32 byte words.
                while (ptrAik != ptrAikEnd) {
                    // k-loop start.

                    assembly {
                        let a := mload(ptrAik) // Load A[i,k].
                        let b := mload(ptrBkj) // Load B[k,j].

                        c := add(c, mul(a, b)) // Add the product `a * b` to `c`.
                    }

                    ptrAik = ptrAik + 32; // Advance to the next column of `A`.
                    ptrBkj = ptrBkj + ptrBRowSize; // Advance to the next row of `B`.
                }

                assembly {
                    mstore(ptrCij, c) // Store the result in C[i,j].
                }

                ptrCij = ptrCij + 32; // Advance to the next element of `C`.
                ptrBj = ptrBj + 32; // Advance to the next column of `B`.
            }

            ptrAi = ptrAi + ptrARowSize; // Advance to the next row of `A`.
        }
    }
}

/// @dev Computes `C_ij = A_ik B_jk`
function dotTransposed(UM256 A, UM256 B) pure returns (UM256 C) {
    unchecked {
        (uint256 nA, uint256 mA, uint256 dataPtrA) = header(A);
        (uint256 nB, uint256 mB, uint256 dataPtrB) = header(B);

        if (mA != mB) revert UM256_IncompatibleDimensions();

        C = mallocUM256(nA, nB);

        uint256 ptrCij = ref(C);

        uint256 ptrARowSize = 32 * mA;
        uint256 ptrBRowSize = 32 * mB;

        uint256 ptrAiEnd = dataPtrA + 32 * nA * mA;
        uint256 ptrAi = dataPtrA; // Updates by row size of `A` in i-loop.

        uint256 ptrBjEnd = dataPtrB + 32 * nB * mB;
        uint256 ptrBj;

        // Loop over `C`s `i` indices.
        while (ptrAi != ptrAiEnd) {
            // i-loop start.

            ptrBj = dataPtrB;

            while (ptrBj != ptrBjEnd) {
                // j-loop start.

                uint256 ptrBjk = ptrBj;
                uint256 ptrAik = ptrAi;
                // End inner loop after one row of `A`.
                uint256 ptrAikEnd = ptrAi + ptrARowSize;

                // Perform the dot product on the current
                // row vector of `A` and the column vector of `B`.
                // Store the result in `c`.
                uint256 c;

                // Loop over 32 byte words.
                while (ptrAik != ptrAikEnd) {
                    // k-loop start.

                    assembly {
                        let a := mload(ptrAik) // Load A[i,k].
                        let b := mload(ptrBjk) // Load B[j,k].

                        c := add(c, mul(a, b)) // Add the product `a * b` to `c`.
                    }

                    ptrAik = ptrAik + 32; // Loop over `A`s columns.
                    ptrBjk = ptrBjk + 32; // Loop over `B`s columns.
                }

                assembly {
                    mstore(ptrCij, c) // Store the result in C[i,j].
                }

                ptrCij = ptrCij + 32; // Advance to the next element of `C`.
                ptrBj = ptrBj + ptrBRowSize; // Advance to the next row of `B`.
            }

            ptrAi = ptrAi + ptrARowSize; // Advance to the next row of `A`.
        }
    }
}

function eq(UM256 A, UM256 B) pure returns (bool equals) {
    unchecked {
        if (UM256.unwrap(A) == UM256.unwrap(B)) return true;

        (uint256 nA, uint256 mA, uint256 ptrA) = header(A);
        (uint256 nB, uint256 mB, uint256 ptrB) = header(B);

        equals = nA == nB && mA == mB;

        // Loop over all `n * m` elements of 32 bytes size.
        uint256 endA = ptrA + nA * mA * 32;

        // Loop over 32 byte words.
        while (ptrA != endA && equals) {
            assembly {
                let a := mload(ptrA)
                let b := mload(ptrB)

                equals := eq(a, b) // Check whether `a == b`.
            }

            // Advance pointers to the next slot.
            ptrA = ptrA + 32;
            ptrB = ptrB + 32;
        }
    }
}

/* ------------- Mat x scalar operators ------------- */

function addScalarUnchecked(UM256 A, uint256 s) pure returns (UM256 C) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrA) = header(A);

        C = mallocUM256(n, m);

        // Loop over all `n * m` elements of 32 bytes size.
        uint256 endA = ptrA + n * m * 32;
        uint256 ptrC = ref(C);

        while (ptrA != endA) {
            assembly {
                let a := mload(ptrA) // Load value at `ptr`.
                let c := add(a, s) // Add value to `s`.

                mstore(ptrC, c) // Store result `c` in `ptrC`.
            }

            // Advance pointers to the next slot.
            ptrA = ptrA + 32;
            ptrC = ptrC + 32;
        }
    }
}

function mulScalarUnchecked(UM256 A, uint256 s) pure returns (UM256 C) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        C = mallocUM256(n, m);

        uint256 ptrA = ptr;
        uint256 endA = ptrA + n * m * 32;
        uint256 ptrC = ref(C);

        while (ptrA != endA) {
            assembly {
                let a := mload(ptrA)
                let c := mul(a, s)

                mstore(ptrC, c)
            }

            // Advance pointers to the next slot.
            ptrA = ptrA + 32;
            ptrC = ptrC + 32;
        }
    }
}

/* ------------- Mat operators ------------- */

function sum(UM256 A) pure returns (uint256 s) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        // Loop over all `n * m` elements of 32 bytes size.
        uint256 end = ptr + n * m * 32;

        while (ptr != end) {
            assembly {
                s := add(s, mload(ptr)) // Load element at `ptr` and add to `s`.
            }

            ptr = ptr + 32; // Advance pointer to the next slot.
        }
    }
}

function eqScalar(UM256 A, uint256 value) pure returns (bool equals) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        equals = true;

        // Loop over all `n * m` elements of 32 bytes size.
        uint256 end = ptr + n * m * 32;

        while (ptr != end) {
            assembly {
                // Load element at `ptr` and compare to `value`.
                equals := eq(mload(ptr), value)
            }

            if (!equals) break; // Exit early.

            ptr = ptr + 32; // Advance pointer to the next slot.
        }
    }
}

function full(uint256 n, uint256 m, uint256 s) pure returns (UM256 C) {
    // Allocate memory for matrix.
    C = mallocUM256(n, m);

    fill_(C, s); // Fill matrix with `s`.
}

function fill_(UM256 A, uint256 a) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        // Loop over n * m elements of 32 bytes.
        uint256 end = ptr + n * m * 32;

        while (ptr != end) {
            assembly {
                mstore(ptr, a) // Store `a` at current pointer location.
            }

            ptr = ptr + 32; // Advance pointer to the next slot.
        }
    }
}

/* ------------- conversions ------------- */

function from_(bytes memory dataBytes, uint256 n, uint256 m) pure returns (UM256 C) {
    unchecked {
        if (n * m * 32 > dataBytes.length) revert UM256_TooLarge();

        uint256 dataPtr;

        assembly {
            dataPtr := add(32, dataBytes) // Actual data is located after length encoding.
        }

        C = UM256Header(dataPtr, n, m);
    }
}

function _bytes(UM256 A) pure returns (bytes memory dataBytes) {
    uint256 ptr = ref(A);

    assembly {
        // This only works under the assumption that
        // we always store the size in bytes before the data.
        dataBytes := sub(ptr, 32)
    }
}

function from(bytes memory dataBytes, uint256 n, uint256 m) view returns (UM256 C) {
    unchecked {
        if (n * m * 32 > dataBytes.length) revert UM256_TooLarge();

        uint256 dataPtr;

        assembly {
            dataPtr := add(32, dataBytes) // Actual data is located after length encoding.
        }

        C = mallocUM256(n, m); // Allocate memory for matrix.

        mcopy(dataPtr, ref(C), n * m * 32); // Copy bytes from `ptrA` to `C`.
    }
}

function copy(UM256 A) view returns (UM256 C) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrA) = header(A);

        C = mallocUM256(n, m); // Allocate memory for matrix.

        mcopy(ptrA, ref(C), n * m * 32); // Copy bytes from `ptrA` to `C`.
    }
}

/* ------------- unsafe conversions ------------- */

function fromArray(uint8[3][4] memory data) view returns (UM256 C) {
    uint256 dataPtr;

    assembly {
        // Making a big assumption here that `data` uint8[3] entries
        // are laid out contiguously in memory right after the pointers.
        // todo: fix this.
        dataPtr := mload(data)
    }

    C = mallocUM256(4, 3); // Allocate memory for matrix.

    mcopy(dataPtr, ref(C), 4 * 3 * 32); // Copy bytes from `dataPtr` to `C`.
}

function fromArray(uint8[3][3] memory data) view returns (UM256 C) {
    uint256 dataPtr;

    assembly {
        dataPtr := mload(data)
    }

    C = mallocUM256(3, 3); // Allocate memory for matrix.

    mcopy(dataPtr, ref(C), 3 * 3 * 32); // Copy bytes from `dataPtr` to `C`.
}

function fromArray(uint8[4][4] memory data) view returns (UM256 C) {
    uint256 dataPtr;

    assembly {
        dataPtr := mload(data)
    }

    C = mallocUM256(4, 4); // Allocate memory for matrix.

    mcopy(dataPtr, ref(C), 4 * 4 * 32); // Copy bytes from `dataPtr` to `C`.
}
