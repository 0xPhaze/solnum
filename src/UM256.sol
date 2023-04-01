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
    bytes_,
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
    T,
    transpose,
    eqAll,
    eqAllScalar,
    // ltAll,
    ltAllScalar,
    lteAllScalar,
    // gtAll,
    gtAllScalar,
    gteAllScalar,
    sum,
    mean,
    vari,
    min,
    max,
    minMax,
    map
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
        uint256 diagSpacing = 32 + n * 32;
        // Loop over n diagonal elements.
        uint256 end = ptr + n * diagSpacing;

        while (ptr != end) {
            assembly {
                mstore(ptr, 1) // Store `1` at current pointer location.
            }

            ptr = ptr + diagSpacing; // Advance pointer to the next slot in the diagonal.
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

                    ptrAik = ptrAik + 32; // Advance to the next column → of `A`.
                    ptrBkj = ptrBkj + ptrBRowSize; // Advance to the next row ↓ of `B`.
                }

                assembly {
                    mstore(ptrCij, c) // Store the result in C[i,j].
                }

                ptrCij = ptrCij + 32; // Advance to the next element of `C`.
                ptrBj = ptrBj + 32; // Advance to the next column → of `B`.
            }

            ptrAi = ptrAi + ptrARowSize; // Advance to the next row ↓ of `A`.
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

                    ptrAik = ptrAik + 32; // Advance to the next column → of `A`.
                    ptrBjk = ptrBjk + 32; // Advance to the next column → of `B`.
                }

                assembly {
                    mstore(ptrCij, c) // Store the result in C[i,j].
                }

                ptrCij = ptrCij + 32; // Advance to the next element of `C`.
                ptrBj = ptrBj + ptrBRowSize; // Advance to the next row ↓ of `B`.
            }

            ptrAi = ptrAi + ptrARowSize; // Advance to the next row ↓ of `A`.
        }
    }
}

function eqAll(UM256 A, UM256 B) pure returns (bool equals) {
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
                let a := mload(ptrA) // Load value at `ptrA`.
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

function min(UM256 A) pure returns (uint256 minValue) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        minValue = type(uint256).max; // Set current min to `0`.

        // Loop over all `n * m` elements of 32 bytes size.
        uint256 end = ptr + n * m * 32;

        while (ptr != end) {
            uint256 a;

            assembly {
                a := mload(ptr) // Load element at `ptr`.
            }

            if (a < minValue) minValue = a; // Replace current min with number.

            ptr = ptr + 32; // Advance pointer to the next slot.
        }
    }
}

function max(UM256 A) pure returns (uint256 maxValue) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        // Loop over all `n * m` elements of 32 bytes size.
        uint256 end = ptr + n * m * 32;

        while (ptr != end) {
            uint256 a;

            assembly {
                a := mload(ptr) // Load element at `ptr`.
            }

            if (a > maxValue) maxValue = a; // Replace current max with number.

            ptr = ptr + 32; // Advance pointer to the next slot.
        }
    }
}

function minMax(UM256 A) pure returns (uint256 minValue, uint256 maxValue) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        minValue = type(uint256).max; // Set current min to `0`.

        // Loop over all `n * m` elements of 32 bytes size.
        uint256 end = ptr + n * m * 32;

        while (ptr != end) {
            uint256 a;

            assembly {
                a := mload(ptr) // Load element at `ptr`.
            }

            if (a > maxValue) maxValue = a; // Replace current max with number.
            if (a < minValue) minValue = a; // Replace current min with number.

            ptr = ptr + 32; // Advance pointer to the next slot.
        }
    }
}

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

function mean(UM256 A) pure returns (uint256 s) {
    unchecked {
        (uint256 n, uint256 m) = shape(A);

        uint256 len = n * m;

        if (len == 0) return 0;

        s = sum(A) / len;
    }
}

// https://en.wikipedia.org/wiki/Algorithms_for_calculating_variance#Computing_shifted_data
function vari(UM256 A) pure returns (uint256 variance) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        uint256 len = n * m;

        if (len < 2) return 0;

        // Loop over all `n * m` elements of 32 bytes size.
        uint256 end = ptr + len * 32;

        // Introduce a shift as the first element.
        uint256 shift;

        assembly {
            shift := mload(ptr)
        }

        ptr = ptr + 32;

        uint256 s;
        uint256 s2;
        while (ptr != end) {
            assembly {
                let aSh := sub(mload(ptr), shift) // Load element at `ptr` and compute shifted element.
                s := add(s, aSh) // Accumulate shifted sums in `s`.
                s2 := add(s2, mul(aSh, aSh)) // Accumulate shifted sums of squares in `s2`.
            }

            ptr = ptr + 32; // Advance pointer to the next slot.
        }

        // todo: double check rounding directions
        variance = ((s2 - (s * s + (len + 1) / 2) / len) + len / 2 - 1) / (len - 1); // note: uses the unbiased version.
            // Use `/ len` for the biased version.
    }
}

function eqAllScalar(UM256 A, uint256 scalar) pure returns (bool equals) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        equals = true; // Set initial value to true.

        // Loop over all `n * m` elements of 32 bytes size.
        uint256 end = ptr + n * m * 32;

        while (ptr != end) {
            assembly {
                let a := mload(ptr) // Load element at `ptr`.

                equals := eq(a, scalar) // Check whether `a == s`.
            }

            if (!equals) break; // Exit early.

            ptr = ptr + 32; // Advance pointer to the next slot.
        }
    }
}

function gtAllScalar(UM256 A, uint256 s) pure returns (bool gtResult) {
    unchecked {
        if (s == type(uint256).max) return gtResult = false; // Exit early.

        gtResult = true; // Set initial value to true.

        (uint256 n, uint256 m, uint256 ptr) = header(A);

        // Loop over all `n * m` elements of 32 bytes size.
        uint256 end = ptr + n * m * 32;

        // Loop over 32 byte words.
        while (ptr != end) {
            assembly {
                let a := mload(ptr) // Load value at `ptr`.

                gtResult := gt(a, s) // Check whether `a > s`.
            }

            if (!gtResult) break; // Exit early.

            ptr = ptr + 32; // Advance pointer to the next slot.
        }
    }
}

function gteAllScalar(UM256 A, uint256 s) pure returns (bool gteResult) {
    unchecked {
        if (s == 0) return gteResult = true; // Exit early.

        gteResult = gtAllScalar(A, s - 1); // Reduce `s` so we can use `gt`.
    }
}

function ltAllScalar(UM256 A, uint256 s) pure returns (bool ltResult) {
    unchecked {
        if (s == 0) return ltResult = false; // Exit early.

        ltResult = true; // Set initial value to true.

        (uint256 n, uint256 m, uint256 ptr) = header(A);

        // Loop over all `n * m` elements of 32 bytes size.
        uint256 end = ptr + n * m * 32;

        // Loop over 32 byte words.
        while (ptr != end) {
            assembly {
                let a := mload(ptr) // Load value at `ptr`.

                ltResult := lt(a, s) // Check whether `a < s`.
            }

            if (!ltResult) break; // Exit early.

            ptr = ptr + 32; // Advance pointer to the next slot.
        }
    }
}

function lteAllScalar(UM256 A, uint256 s) pure returns (bool lteResult) {
    unchecked {
        if (s == type(uint256).max) return lteResult = true; // Exit early.

        lteResult = ltAllScalar(A, s + 1); // Increase by `1` and use `ltAllScalar`.
    }
}

function full(uint256 n, uint256 m, uint256 s) pure returns (UM256 C) {
    C = mallocUM256(n, m); // Allocate memory for matrix.

    fill_(C, s); // Fill matrix with `s`.
}

function fillZeros_(UM256 A) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        // Size is n * m elements of 32 bytes.
        uint256 size = n * m * 32;

        assembly {
            // Copy non-existent calldata to fill with zeros.
            calldatacopy(ptr, calldatasize(), size)
        }
    }
}

function fill_(UM256 A, uint256 a) pure {
    unchecked {
        // Optimization for filling zeros.
        if (a == 0) return fillZeros_(A);

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

function T(UM256 A) pure returns (UM256 C) {
    C = transpose(A);
}

function transpose(UM256 A) pure returns (UM256 C) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrAj) = header(A);

        if (n == 1 || m == 1) return C = A.reshape(m, n);

        C = mallocUM256(m, n); // Allocate memory for matrix.

        uint256 ptrCi = ref(C);

        uint256 ptrARow = 32 * m;
        uint256 ptrCRow = 32 * n;
        // End iterating over `A`s columns when arriving at the last column.
        uint256 ptrAjEnd = ptrAj + ptrARow;

        // Loop over `A`s rows.
        while (ptrAj != ptrAjEnd) {
            uint256 ptrA = ptrAj; // Start at the beginning of the current column.
            uint256 ptrC = ptrCi; // Start at the beginning of the current row.
            uint256 ptrCEnd = ptrCi + ptrCRow; // End at the end of the current row.

            // Loop over `C`s columns.
            while (ptrC != ptrCEnd) {
                assembly {
                    mstore(ptrC, mload(ptrA)) // Copy element from `A` to `B`.
                }

                ptrC = ptrC + 32; // Advance to the next column →.
                ptrA = ptrA + ptrARow; // Advance to the next row ↓.
            }

            ptrAj = ptrAj + 32; // Advance to the next column → of `A`.
            ptrCi = ptrCi + ptrCRow; // Advance to the next row ↓ of `C`.
        }
    }
}

function map(UM256 A, function (uint256) returns (uint256) fn) returns (UM256 C) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrA) = header(A);

        C = mallocUM256(m, n); // Allocate memory for matrix.

        uint256 ptrC = ref(C); // Obtain a pointer to `C`s data location.

        // Loop over all `n * m` elements of 32 bytes size.
        uint256 end = ptrA + n * m * 32;

        while (ptrA != end) {
            uint256 a;

            assembly {
                a := mload(ptrA) // Load element at `ptrA`.
            }

            uint256 c = fn(a);

            assembly {
                mstore(ptrC, c) // Store `c` at `ptrC`.
            }

            ptrA = ptrA + 32; // Advance pointer to the next slot.
            ptrC = ptrC + 32; // Advance pointer to the next slot.
        }
    }
}

/* ------------- conversions ------------- */

function copy(UM256 A) view returns (UM256 C) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrA) = header(A);

        C = mallocUM256(n, m); // Allocate memory for matrix.

        mcopy(ptrA, ref(C), n * m * 32); // Copy bytes from `ptrA` to `C`.
    }
}

function fromAbiEncoded_(bytes memory dataBytes) pure returns (UM256 C) {
    C = fromAbiEncoded_(dataBytes, 1, dataBytes.length / 32);
}

function fromAbiEncoded_(bytes memory dataBytes, uint256 n, uint256 m) pure returns (UM256 C) {
    unchecked {
        if (n * m * 32 > dataBytes.length) revert UM256_TooLarge();

        uint256 dataPtr;

        assembly {
            dataPtr := add(32, dataBytes) // Actual data is located after length encoding.
        }

        C = UM256Header(dataPtr, n, m); // Generate header without allocating memory.
    }
}

function fromAbiEncoded(bytes memory dataBytes) view returns (UM256 C) {
    C = fromAbiEncoded(dataBytes, 1, dataBytes.length / 32);
}

function fromAbiEncoded(bytes memory dataBytes, uint256 n, uint256 m) view returns (UM256 C) {
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

function bytes_(UM256 A) pure returns (bytes memory dataBytes) {
    uint256 ptr = ref(A); // Obtain a pointer to `A`s data location.

    assembly {
        // This only works under the assumption that
        // we always store the size in bytes before the data.
        dataBytes := sub(ptr, 32)
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
