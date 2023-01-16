// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";
import "./UM256.sol" as UM256Lib;
import "./N32x32.sol" as __N32x32;

type M32x32 is uint256;

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
    setUnsafe,
    setIndex,
    fill_,
    add,
    addScalar,
    addScalarTo_,
    addScalarUnchecked,
    addScalarUncheckedTo_,
    mulScalar,
    mulScalarTo_,
    mulScalarUnchecked,
    mulScalarUncheckedTo_,
    add,
    dot,
    dotTransposed,
    eq,
    eqScalar,
    sum
} for M32x32 global;

error M32x32_TooLarge();
error M32x32_InvalidRange();
error M32x32_IndexOutOfBounds();
error M32x32_InvalidDimensions();
error M32x32_IncompatibleDimensions();

uint256 constant _UINT64_MAX = 0xffffffffffffffff;
uint256 constant MAX_64_BITS = 0xffffffffffffffff;
uint256 constant OVERFLOW_CHECK_INT64 = 0x8000000000000000;

/* ------------- header ------------- */

struct M32x32HeaderStruct {
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

function M32x32Header(uint256 ptr, uint256 n, uint256 m) pure returns (M32x32 A) {
    A = M32x32.wrap(
        ptr << 48 // data location
            | m << 24 | n // shape
    );

    if ((n | m | (ptr >> 40)) > UM256Lib.MAX_24_BITS) revert M32x32_TooLarge();
}

function header(M32x32 A) pure returns (uint256 n, uint256 m, uint256 ptr) {
    n = (M32x32.unwrap(A)) & UM256Lib.MAX_24_BITS;
    m = (M32x32.unwrap(A) >> 24) & UM256Lib.MAX_24_BITS;
    ptr = (M32x32.unwrap(A) >> 48) & _UINT64_MAX;
}

function shape(M32x32 A) pure returns (uint256 n, uint256 m) {
    n = (M32x32.unwrap(A)) & UM256Lib.MAX_24_BITS;
    m = (M32x32.unwrap(A) >> 24) & UM256Lib.MAX_24_BITS;
}

function dim0(M32x32 A) pure returns (uint256 n) {
    n = (M32x32.unwrap(A)) & UM256Lib.MAX_24_BITS;
}

function dim1(M32x32 A) pure returns (uint256 m) {
    m = (M32x32.unwrap(A) >> 24) & UM256Lib.MAX_24_BITS;
}

function length(M32x32 A) pure returns (uint256 len) {
    unchecked {
        uint256 n = (M32x32.unwrap(A)) & UM256Lib.MAX_24_BITS;
        uint256 m = (M32x32.unwrap(A) >> 24) & UM256Lib.MAX_24_BITS;

        len = n * m;
    }
}

function sizeBytes(M32x32 A) pure returns (uint256 size) {
    unchecked {
        uint256 n = (M32x32.unwrap(A)) & UM256Lib.MAX_24_BITS;
        uint256 m = (M32x32.unwrap(A) >> 24) & UM256Lib.MAX_24_BITS;

        size = n * m * 8;
    }
}

function ref(M32x32 A) pure returns (uint256 ptr) {
    ptr = (M32x32.unwrap(A) >> 48) & _UINT64_MAX;
}

/* ------------- constructors ------------- */

function mallocM32x32(uint256 n, uint256 m) pure returns (M32x32 A) {
    unchecked {
        // Memory size in bytes.
        uint256 size = n * m * 8;
        // Round up the size allocated in memory to 32 bytes.
        uint256 msize = (size + 31) & (~uint256(31));
        // Allocate memory space for matrix.
        // Add 32 bytes to store the byte size.
        uint256 ptr = UM256Lib.malloc(32 + msize);

        assembly {
            mstore(ptr, size) // Store the bytes size.
        }

        // Generate metadata header, skip the 32 bytes length.
        // This is only for convenience when converting to `bytes`.
        A = M32x32Header(ptr + 32, n, m);
    }
}

function zeros(uint256 n, uint256 m) pure returns (M32x32 C) {
    C = mallocM32x32(n, m); // Allocate memory for matrix.

    // Fill matrix with `0`s.
    fill_(C, 0);
}

function ones(uint256 n, uint256 m) pure returns (M32x32 C) {
    // Allocate memory for matrix.
    C = mallocM32x32(n, m);

    // Fill matrix with `1`s.
    fill_(C, 1);
}

function eye(uint256 n, uint256 m) pure returns (M32x32 C) {
    unchecked {
        // Only allowing square dimensions.
        if (n != m) revert M32x32_InvalidDimensions();

        // Allocate memory for matrix.
        C = mallocM32x32(n, m);

        // Fill matrix with `0`s.
        fill_(C, 0);

        // Obtain a pointer to matrix data location.
        // Offset pointer to the left by 3 chunks so that
        // the loaded chunk will be right-aligned.
        uint256 ptr = ref(C) - 24;
        // Spacing in memory between the elements on the diagonal.
        uint256 diagSpace = 8 + n * 8;
        // Loop over all `n` diagonal elements.
        uint256 end = ptr + n * diagSpace;

        // TODO: optimize by looping over chunks.
        // Don't need to concat with word.
        while (ptr != end) {
            assembly {
                let word := and(mload(ptr), not(_UINT64_MAX))

                mstore(ptr, or(1, word))
            }

            ptr = ptr + diagSpace; // Advance pointer to the next slot in the diagonal.
        }
    }
}

function range(uint256 start, uint256 end) pure returns (M32x32 C) {
    unchecked {
        // `start <= end` must hold.
        if (start > end) revert M32x32_InvalidRange();

        uint256 numEl = end - start;

        // Allocate memory for matrix.
        C = mallocM32x32(1, numEl);

        // Obtain a pointer to matrix data location.
        // Offset pointer to the left by 3 chunks so that
        // the loaded chunk will be right-aligned.
        uint256 ptr = ref(C);

        uint256 a = start;
        uint256 aEnd = a + (numEl + 3 & ~uint256(3));

        while (a != aEnd) {
            uint256 word = packWordUnsafe(a, a + 1, a + 2, a + 3);

            assembly {
                mstore(ptr, word) // Store `a` at current pointer location.
            }

            ptr = ptr + 32; // Advance pointer to the next slot.
            a = a + 4;
        }
    }
}

function range(uint256 end) pure returns (M32x32 C) {
    return range(0, end);
}

function reshape(M32x32 A, uint256 nNew, uint256 mNew) pure returns (M32x32 out) {
    unchecked {
        (uint256 n, uint256 m, uint256 data) = header(A);

        if (n * m != nNew * mNew) revert M32x32_InvalidDimensions();

        out = M32x32Header(data, nNew, mNew);
    }
}

/* ------------- indexing ------------- */

// TODO convert to N32x32
function atIndex(M32x32 A, uint256 index) pure returns (uint256 a) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        if (index >= n * m) revert M32x32_IndexOutOfBounds();

        ptr = ptr + 8 * (index - 3);

        assembly {
            a := and(mload(ptr), _UINT64_MAX)
        }
    }
}

function setIndex(M32x32 A, uint256 index, uint256 value) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        if (index >= n * m) revert M32x32_IndexOutOfBounds();

        ptr = ptr + 8 * (index - 3);

        assembly {
            let word := and(mload(ptr), not(_UINT64_MAX))

            mstore(ptr, or(value, word))
        }
    }
}

function at(M32x32 A, uint256 i, uint256 j) pure returns (uint256 a) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        if (i >= n || j >= m) revert M32x32_IndexOutOfBounds();

        ptr = ptr + 8 * (i * m + j - 3);

        assembly {
            a := and(mload(ptr), _UINT64_MAX)
        }
    }
}

function set(M32x32 A, uint256 i, uint256 j, uint256 value) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        if (i >= n || j >= m) revert M32x32_IndexOutOfBounds();

        ptr = ptr + 8 * (i * m + j - 3);

        assembly {
            let word := and(mload(ptr), not(_UINT64_MAX))

            mstore(ptr, or(value, word))
        }
    }
}

function setUnsafe(M32x32 A, uint256 i, uint256 j, uint256 value) pure {
    unchecked {
        (, uint256 m, uint256 ptr) = header(A);

        ptr = ptr + 8 * (uint256(i) * m + uint256(j) - 3);

        assembly {
            let word := and(mload(ptr), not(_UINT64_MAX))

            mstore(ptr, or(value, word))
        }
    }
}

/* ------------- Mat x Mat operators ------------- */

function addUnchecked(M32x32 A, M32x32 B) pure returns (M32x32 C) {
    (uint256 n, uint256 m) = A.shape();

    // Allocate new matrix of the same dimensions.
    C = mallocM32x32(n, m);

    // Add scalar `A` and `B`, store result in `C`.
    addUncheckedTo_(A, B, C);
}

function addUncheckedTo_(M32x32 A, M32x32 B, M32x32 C) pure {
    unchecked {
        (uint256 nA, uint256 mA, uint256 ptrA) = header(A);
        (uint256 nB, uint256 mB, uint256 ptrB) = header(B);

        if (nA != nB || mA != mB) revert M32x32_IncompatibleDimensions();

        // Loop over all `nA * mA` elements of 8 bytes.
        uint256 size = nA * mA * 8;
        // Up until here we can load & parse full words.
        uint256 endA = ptrA + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = ptrA + size - endA;
        // Obtain a pointer to `C`s data location.
        uint256 ptrC = ref(C);

        while (ptrA != endA) {
            assembly {
                let a := mload(ptrA) // Load 4 values from `A` at `ptrA`.
                let b := mload(ptrB) // Load 4 values from `B` at `ptrB`.
                let c := add(a, b) // Add packed values together.

                mstore(ptrC, c) // Store packed values in `ptrC`.
            }

            // Advance pointers to the next slot.
            ptrA = ptrA + 32;
            ptrB = ptrB + 32;
            ptrC = ptrC + 32;
        }

        // Parse the last remaining word.
        if (rest != 0) {
            assembly {
                // Mask applies to leftover bits in word.
                let mask := not(shr(mul(rest, 8), not(0)))
                let a := mload(ptrA) // Load packed values from `A` at `ptrA`.
                let b := mload(ptrB) // Load packed values from `B` at `ptrB`.
                // Apply mask to clear out any unwanted right-aligned bits.
                let c := add(and(a, mask), and(b, mask)) // Add packed values together.

                mstore(ptrC, c) // Store packed `c` in `ptrC`.
            }
        }
    }
}

function add(M32x32 A, M32x32 B) pure returns (M32x32 C) {
    (uint256 n, uint256 m) = A.shape();

    // Allocate new matrix of the same dimensions.
    C = mallocM32x32(n, m);

    // Add scalar `A` and `B`, store result in `C`.
    addTo_(A, B, C);
}

function addTo_(M32x32 A, M32x32 B, M32x32 C) pure {
    unchecked {
        (uint256 nA, uint256 mA, uint256 ptrA) = header(A);
        (uint256 nB, uint256 mB, uint256 ptrB) = header(B);

        if (nA != nB || mA != mB) revert M32x32_IncompatibleDimensions();

        // Loop over all `nA * mA` elements of 8 bytes.
        uint256 size = nA * mA * 8;
        // Up until here we can load & parse full words.
        uint256 endA = ptrA + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = ptrA + size - endA;
        // Obtain a pointer to `C`s data location.
        uint256 ptrC = ref(C);

        // Keep track of over/underflows.
        uint256 overflow;

        // Loop over 32 byte words.
        while (ptrA != endA) {
            assembly {
                let a := mload(ptrA) // Load 4 values from `A` at `ptrA`.
                let b := mload(ptrB) // Load 4 values from `B` at `ptrB`.
                let c := add(a, b) // Add packed values together.

                mstore(ptrC, c) // Store packed values in `ptrC`.

                overflow := or(overflow, add(add(and(a, _UINT64_MAX), and(b, _UINT64_MAX)), OVERFLOW_CHECK_INT64)) // forgefmt: disable-line
                overflow := or(overflow, add(add(and(shr(64, a), _UINT64_MAX), and(shr(64, b), _UINT64_MAX)), OVERFLOW_CHECK_INT64)) // forgefmt: disable-line
                overflow := or(overflow, add(add(and(shr(128, a), _UINT64_MAX), and(shr(128, b), _UINT64_MAX)), OVERFLOW_CHECK_INT64)) // forgefmt: disable-line
                overflow := or(overflow, add(add(shr(192, a), and(shr(192, b), _UINT64_MAX)), OVERFLOW_CHECK_INT64)) // forgefmt: disable-line
            }

            // Advance pointers to the next slot.
            ptrA = ptrA + 32;
            ptrB = ptrB + 32;
            ptrC = ptrC + 32;
        }

        // Parse the last remaining word.
        if (rest != 0) {
            assembly {
                // Mask applies to leftover bits in word.
                let mask := not(shr(mul(rest, 8), not(0)))
                let a := and(mload(ptrA), mask) // Load packed values from `A` at `ptrA`.
                let b := and(mload(ptrB), mask) // Load packed values from `B` at `ptrB`.
                // Apply mask to clear out any unwanted right-aligned bits.
                let c := add(and(a, mask), and(b, mask)) // Add packed values together.

                mstore(ptrC, c) // Store packed `c` in `ptrC`.

                overflow := or(overflow, add(add(and(shr(64, a), _UINT64_MAX), and(shr(64, b), _UINT64_MAX)), OVERFLOW_CHECK_INT64)) // forgefmt: disable-line
                overflow := or(overflow, add(add(and(shr(128, a), _UINT64_MAX), and(shr(128, b), _UINT64_MAX)), OVERFLOW_CHECK_INT64)) // forgefmt: disable-line
                overflow := or(overflow, add(add(shr(192, a), and(shr(192, b), _UINT64_MAX)), OVERFLOW_CHECK_INT64)) // forgefmt: disable-line
            }
        }

        if (overflow > _UINT64_MAX) revert __N32x32.N32x32_Overflow();
    }
}

/// Perform the matrix multiplication given by:
/// `C_ij = A_ik B_kj`
///
/// Given `i`, `j`, `k`, the offsets
/// of the elements in `A`, `B` to be summed are:
/// `ptrA = 8 * (k + i * mA)`
/// `ptrB = 8 * (j + k * mb)`
function dot(M32x32 A, M32x32 B) pure returns (M32x32 C) {
    unchecked {
        (uint256 nA, uint256 mA, uint256 dataPtrA) = header(A);
        (uint256 nB, uint256 mB, uint256 dataPtrB) = header(B);

        if (mA != nB) revert M32x32_IncompatibleDimensions();

        C = mallocM32x32(nA, mB);

        uint256 ptrCij = ref(C);

        uint256 ptrARowSize = 8 * mA;
        uint256 ptrBRowSize = 8 * mB;

        uint256 ptrAiEnd = dataPtrA + 8 * nA * mA;
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

                        // c := add(c, mul(a, b)) // Add the product `a * b` to `c`.

                        let s
                        s := mul(and(a, _UINT64_MAX), and(b, _UINT64_MAX))
                        c := add(c, s)
                        s := mul(and(shr(64, a), _UINT64_MAX), and(shr(64, b), _UINT64_MAX))
                        c := add(c, s)
                        s := mul(and(shr(128, a), _UINT64_MAX), and(shr(128, b), _UINT64_MAX))
                        c := add(c, s)
                        s := mul(shr(192, a), shr(192, b))
                        c := add(c, s)

                        // overflow := or(overflow, add(s, OVERFLOW_CHECK_INT64))
                    }

                    ptrAik = ptrAik + 32; // Advance to the next column of `A`.
                    ptrBkj = ptrBkj + ptrBRowSize; // Advance to the next row of `B`.
                }

                // // Loop over 32 byte words.
                // while (ptrA != endA) {
                //     assembly {
                //         let a := mload(ptrA) // Load 4 values from `A` at `ptrA`.
                //         let b := mload(ptrB) // Load 4 values from `B` at `ptrB`.
                //         let c := add(a, b) // Add packed values together.

                //         mstore(ptrC, c) // Store packed values in `ptrC`.

                //             overflow := or(overflow, add(add(and(a, _UINT64_MAX), and(b, _UINT64_MAX)), OVERFLOW_CHECK_INT64)) // forgefmt: disable-line
                //             overflow := or(overflow, add(add(and(shr(64, a), _UINT64_MAX), and(shr(64, b), _UINT64_MAX)), OVERFLOW_CHECK_INT64)) // forgefmt: disable-line
                //             overflow := or(overflow, add(add(and(shr(128, a), _UINT64_MAX), and(shr(128, b), _UINT64_MAX)), OVERFLOW_CHECK_INT64)) // forgefmt: disable-line
                //             overflow := or(overflow, add(add(shr(192, a), and(shr(192, b), _UINT64_MAX)), OVERFLOW_CHECK_INT64)) // forgefmt: disable-line
                //     }

                //     // Advance pointers to the next slot.
                //     ptrA = ptrA + 32;
                //     ptrB = ptrB + 32;
                //     ptrC = ptrC + 32;
                // }

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
function dotTransposed(M32x32 A, M32x32 B) pure returns (M32x32 C) {
    unchecked {
        (uint256 nA, uint256 mA, uint256 dataPtrA) = header(A);
        (uint256 nB, uint256 mB, uint256 dataPtrB) = header(B);

        if (mA != mB) revert M32x32_IncompatibleDimensions();

        C = mallocM32x32(nA, nB);

        uint256 ptrCij = ref(C);

        uint256 ptrARowSize = 8 * mA;
        uint256 ptrBRowSize = 8 * mB;

        uint256 ptrAiEnd = dataPtrA + 8 * nA * mA;
        uint256 ptrAi = dataPtrA; // Updates by row size of `A` in i-loop.

        uint256 ptrBjEnd = dataPtrB + 8 * nB * mB;
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

                        let s
                        s := mul(and(a, _UINT64_MAX), and(b, _UINT64_MAX))
                        c := add(c, s)
                        s := mul(and(shr(64, a), _UINT64_MAX), and(shr(64, b), _UINT64_MAX))
                        c := add(c, s)
                        s := mul(and(shr(128, a), _UINT64_MAX), and(shr(128, b), _UINT64_MAX))
                        c := add(c, s)
                        s := mul(shr(192, a), shr(192, b))
                        c := add(c, s)

                        // c := add(c, mul(a, b)) // Add the product `a * b` to `c`.
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

function eq(M32x32 A, M32x32 B) pure returns (bool equals) {
    unchecked {
        if (M32x32.unwrap(A) == M32x32.unwrap(B)) return true;

        (uint256 nA, uint256 mA, uint256 ptrA) = header(A);
        (uint256 nB, uint256 mB, uint256 ptrB) = header(B);

        equals = nA == nB && mA == mB;

        // Loop over all `n * m` elements of 8 bytes.
        uint256 size = nA * mA * 8;
        // Up until here we can load & parse full words.
        uint256 endA = ptrA + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = ptrA + size - endA;

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

        uint256 wordA;
        uint256 wordB;

        assembly {
            wordA := mload(ptrA)
            wordB := mload(ptrB)
        }

        // Parse the last remaining word in chunks of 8 bytes.
        while (rest != 0) {
            uint256 a = (wordA >> ((32 - rest) * 8)) & _UINT64_MAX;
            uint256 b = (wordB >> ((32 - rest) * 8)) & _UINT64_MAX;

            equals = equals && (a == b);
            rest = rest - 8;
        }
    }
}

/* ------------- Mat x scalar operators ------------- */

function addScalarUnchecked(M32x32 A, uint256 s) pure returns (M32x32 C) {
    (uint256 n, uint256 m) = A.shape();

    // Allocate new matrix of the same dimensions.
    C = mallocM32x32(n, m);

    // Add scalar `s` to `A`, store result in `C`.
    addScalarUncheckedTo_(A, s, C);
}

function addScalar(M32x32 A, uint256 s) pure returns (M32x32 C) {
    (uint256 n, uint256 m) = A.shape();

    // Allocate new matrix of the same dimensions.
    C = mallocM32x32(n, m);

    // Add scalar `s` to `A`, store result in `C`.
    addScalarTo_(A, s, C);
}

function addScalarUncheckedTo_(M32x32 A, uint256 s, M32x32 C) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrA) = header(A);

        // Loop over all `n * m` elements of 8 bytes.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words.
        uint256 endA = ptrA + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = ptrA + size - endA;
        // Pack `s` in one word for efficiency.
        uint256 valueX4 = packWordUnsafe(s, s, s, s);
        // Obtain a pointer to `C`s data location.
        uint256 ptrC = ref(C);

        // Loop over 32 byte words.
        while (ptrA != endA) {
            assembly {
                let a := mload(ptrA) // Load 4 values from `A` at `ptrA`.
                let c := add(a, valueX4) // Add packed values together.

                mstore(ptrC, c) // Store packed `c` in `ptrC`.
            }

            // Advance pointers to the next slot.
            ptrA = ptrA + 32;
            ptrC = ptrC + 32;
        }

        // Parse the last remaining word.
        if (rest != 0) {
            assembly {
                // Mask applies to leftover bits in word.
                let mask := not(shr(mul(rest, 8), not(0)))
                // Load packed values from `A` at `ptrA`.
                let a := mload(ptrA)
                // Apply mask to clear out any unwanted right-aligned bits.
                let c := add(and(a, mask), and(valueX4, mask)) // Add packed values together.

                mstore(ptrC, c) // Store packed `c` in `ptrC`.
            }
        }
    }
}

function addScalarTo_(M32x32 A, uint256 s, M32x32 C) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrA) = header(A);

        // Loop over all `n * m` elements of 8 bytes.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words.
        uint256 endA = ptrA + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = ptrA + size - endA;
        // Pack `s` in one word for efficiency.
        uint256 valueX4 = packWordUnsafe(s, s, s, s);
        // Obtain a pointer to `C`s data location.
        uint256 ptrC = ref(C);

        // Keep track of over/underflows.
        uint256 overflow;

        // Loop over 32 byte words.
        while (ptrA != endA) {
            assembly {
                let a := mload(ptrA) // Load 4 values from `A` at `ptrA`.
                let c := add(a, valueX4) // Add packed values together.

                mstore(ptrC, c) // Store packed `c` in `ptrC`.

                overflow := or(overflow, add(add(and(a, _UINT64_MAX), s), OVERFLOW_CHECK_INT64))
                overflow := or(overflow, add(add(and(shr(64, a), _UINT64_MAX), s), OVERFLOW_CHECK_INT64))
                overflow := or(overflow, add(add(and(shr(128, a), _UINT64_MAX), s), OVERFLOW_CHECK_INT64))
                overflow := or(overflow, add(add(shr(192, a), s), OVERFLOW_CHECK_INT64))
            }

            // Advance pointers to the next slot.
            ptrA = ptrA + 32;
            ptrC = ptrC + 32;
        }

        // Parse the last remaining word.
        if (rest != 0) {
            assembly {
                // Mask applies to leftover bits in word.
                let mask := not(shr(mul(rest, 8), not(0)))
                // Load packed values from `A` at `ptrA`.
                let a := and(mload(ptrA), mask)
                // Apply mask to clear out any unwanted right-aligned bits.
                let c := add(a, and(valueX4, mask)) // Add packed values together.

                mstore(ptrC, c) // Store packed `c` in `ptrC`.

                overflow := or(overflow, add(add(and(shr(64, a), _UINT64_MAX), s), OVERFLOW_CHECK_INT64))
                overflow := or(overflow, add(add(and(shr(128, a), _UINT64_MAX), s), OVERFLOW_CHECK_INT64))
                overflow := or(overflow, add(add(shr(192, a), s), OVERFLOW_CHECK_INT64))
            }
        }

        if (overflow > _UINT64_MAX) revert __N32x32.N32x32_Overflow();
    }
}

function mulScalarUnchecked(M32x32 A, uint256 s) pure returns (M32x32 C) {
    (uint256 n, uint256 m) = A.shape();

    // Allocate new matrix of the same dimensions.
    C = mallocM32x32(n, m);

    // Multiply `A` with scalar `s`, store result in `C`.
    mulScalarUncheckedTo_(A, s, C);
}

function mulScalar(M32x32 A, uint256 s) pure returns (M32x32 C) {
    (uint256 n, uint256 m) = A.shape();

    // Allocate new matrix of the same dimensions.
    C = mallocM32x32(n, m);

    // Multiply `A` with scalar `s`, store result in `C`.
    mulScalarTo_(A, s, C);
}

function mulScalarUncheckedTo_(M32x32 A, uint256 s, M32x32 C) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrA) = header(A);

        // Loop over all `n * m` elements of 8 bytes.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words.
        uint256 endA = ptrA + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = ptrA + size - endA;
        // Obtain a pointer to `C`s data location.
        uint256 ptrC = ref(C);

        // Loop over 32 byte words.
        while (ptrA != endA) {
            assembly {
                let a := mload(ptrA) // Load 4 values from `A` at `ptrA`.
                let c := mul(a, s) // Multiply packed values together.

                mstore(ptrC, c) // Store packed `c` in `ptrC`.
            }

            // Advance pointers to the next slot.
            ptrA = ptrA + 32;
            ptrC = ptrC + 32;
        }

        // Parse the last remaining word in chunks of 8 bytes.
        if (rest != 0) {
            assembly {
                // Mask applies to leftover bits in word.
                let mask := not(shr(mul(rest, 8), not(0)))
                // Load packed values from `A` at `ptrA`.
                let a := mload(ptrA)
                // Apply mask to clear out any unwanted right-aligned bits.
                let c := mul(and(a, mask), s) // Multiply packed values together.

                mstore(ptrC, c) // Store packed `c` in `ptrC`.
            }
        }
    }
}

function mulScalarTo_(M32x32 A, uint256 s, M32x32 C) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrA) = header(A);

        // Loop over all `n * m` elements of 8 bytes.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words.
        uint256 endA = ptrA + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = ptrA + size - endA;
        // Obtain a pointer to `C`s data location.
        uint256 ptrC = ref(C);
        // Keep track of over/underflows.
        uint256 overflow;

        // Loop over 32 byte words.
        while (ptrA != endA) {
            assembly {
                let a := mload(ptrA) // Load 4 values from `A` at `ptrA`.
                let c := mul(a, s) // Multiply packed values together.

                mstore(ptrC, c) // Store packed `c` in `ptrC`.

                // Check for over/underflows.
                overflow := or(overflow, add(mul(and(a, _UINT64_MAX), s), OVERFLOW_CHECK_INT64))
                overflow := or(overflow, add(mul(and(shr(64, a), _UINT64_MAX), s), OVERFLOW_CHECK_INT64))
                overflow := or(overflow, add(mul(and(shr(128, a), _UINT64_MAX), s), OVERFLOW_CHECK_INT64))
                overflow := or(overflow, add(mul(shr(192, a), s), OVERFLOW_CHECK_INT64))
            }

            // Advance pointers to the next slot.
            ptrA = ptrA + 32;
            ptrC = ptrC + 32;
        }

        // Parse the last remaining word in chunks of 8 bytes.
        if (rest != 0) {
            assembly {
                // Mask applies to leftover bits in word.
                let mask := not(shr(mul(rest, 8), not(0)))
                // Load packed values from `A` at `ptrA`.
                let a := and(mload(ptrA), mask)
                // Apply mask to clear out any unwanted right-aligned bits.
                let c := mul(and(a, mask), s) // Multiply packed values together.

                mstore(ptrC, c) // Store packed `c` in `ptrC`.

                overflow := or(overflow, add(mul(and(shr(64, a), _UINT64_MAX), s), OVERFLOW_CHECK_INT64))
                overflow := or(overflow, add(mul(and(shr(128, a), _UINT64_MAX), s), OVERFLOW_CHECK_INT64))
                overflow := or(overflow, add(mul(shr(192, a), s), OVERFLOW_CHECK_INT64))
            }
        }

        if (overflow > _UINT64_MAX) revert __N32x32.N32x32_Overflow();
    }
}

/* ------------- Mat operators ------------- */

function sum(M32x32 A) pure returns (uint256 s) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        // Loop over all `n * m` elements of 8 bytes.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words.
        uint256 end = ptr + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = ptr + size - end;

        // Loop over 32 byte words.
        while (ptr != end) {
            assembly {
                let word := mload(ptr) // Load word at `ptr`.

                // Add each chunk together to `s`.
                s := add(s, and(word, _UINT64_MAX))
                s := add(s, and(shr(64, word), _UINT64_MAX))
                s := add(s, and(shr(128, word), _UINT64_MAX))
                s := add(s, shr(192, word))
            }

            ptr = ptr + 32; // Advance pointer to the next slot.
        }

        uint256 word;

        assembly {
            word := mload(ptr)
        }

        // Parse the last remaining word in chunks of 8 bytes.
        while (rest != 0) {
            uint256 a = (word >> ((32 - rest) * 8)) & _UINT64_MAX;

            s = s + a;
            rest = rest - 8;
        }
    }
}

function eqScalar(M32x32 A, uint256 value) pure returns (bool equals) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        // Loop over all `n * m` elements of 8 bytes size.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words.
        uint256 end = ptr + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = ptr + size - end;
        // Pack `value` in one word for efficiency.
        uint256 valueX4 = packWordUnsafe(value, value, value, value);

        equals = true;

        // Loop over 32 byte words.
        while (ptr != end) {
            assembly {
                // Load packed elements at `ptr` and compare to `value`.
                equals := eq(mload(ptr), valueX4)
            }

            if (!equals) break; // Exit early.

            ptr = ptr + 32; // Advance pointer to the next slot.
        }

        uint256 word;

        assembly {
            word := mload(ptr)
        }

        // Parse the last remaining word in chunks of 8 bytes.
        while (rest != 0) {
            uint256 a = (word >> ((32 - rest) * 8)) & _UINT64_MAX;

            equals = equals && (a == value);
            rest = rest - 8;
        }
    }
}

function full(uint256 n, uint256 m, uint256 s) pure returns (M32x32 C) {
    C = mallocM32x32(n, m); // Allocate memory for matrix.

    fill_(C, s); // Fill matrix with `s`.
}

function fill_(M32x32 A, uint256 s) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        // Loop over all `n * m` elements of 8 bytes.
        uint256 end = ptr + ((n * m * 8 + 31) & ~uint256(31));

        // Pack `value` in one word for efficiency.
        uint256 sX4 = packWordUnsafe(s, s, s, s);

        // NOTE: If length is not divisible by 4 we are overshooting.
        while (ptr != end) {
            assembly {
                mstore(ptr, sX4) // Store `s` at current pointer location in all 4 chunks.
            }

            ptr = ptr + 32; // Advance pointer to the next slot.
        }
    }
}

/* ------------- conversions ------------- */

function from_(bytes memory dataBytes, uint256 n, uint256 m) pure returns (M32x32 C) {
    unchecked {
        if (n * m * 8 > dataBytes.length) revert M32x32_TooLarge();

        uint256 dataPtr;

        assembly {
            dataPtr := add(32, dataBytes) // Actual data is located after length encoding.
        }

        C = M32x32Header(dataPtr, n, m);
    }
}

function _bytes(M32x32 A) pure returns (bytes memory dataBytes) {
    uint256 ptr = ref(A);

    assembly {
        // This only works under the assumption that
        // we always store the size in bytes before the data.
        dataBytes := sub(ptr, 32)
    }
}

function from(bytes memory dataBytes, uint256 n, uint256 m) view returns (M32x32 C) {
    unchecked {
        if (n * m * 8 > dataBytes.length) revert M32x32_TooLarge();

        uint256 dataPtr;

        assembly {
            dataPtr := add(32, dataBytes) // Actual data is located after length encoding.
        }

        C = mallocM32x32(n, m); // Allocate memory for matrix.

        UM256Lib.mcopy(dataPtr, ref(C), n * m * 8); // Copy data from `ptrA` to `ptrC`.
    }
}

function copy(M32x32 A) view returns (M32x32 C) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrA) = header(A);

        C = mallocM32x32(n, m); // Allocate memory for matrix.

        UM256Lib.mcopy(ptrA, ref(C), n * m * 8); // Copy data from `ptrA` to `ptrC`.
    }
}

/* ------------- conversions ------------- */

function fromArray(uint8[3][3] memory data) pure returns (M32x32 C) {
    C = mallocM32x32(3, 3); // Allocate new matrix of the same dimensions.

    uint256 ptr;

    assembly {
        // Making a big assumption here that `data` uint8[3] entries
        // are laid out contiguously in memory right after the pointers.
        ptr := mload(data)
    }

    C = mallocM32x32(3, 3); // Allocate memory for matrix.

    // Add scalar `A` and `B`, store result in `C`.
    copyFromUint256PtrToUnsafe_(ptr, 3, 3, C);
}

function fromArray(uint8[4][2] memory data) pure returns (M32x32 C) {
    uint256 ptr;

    assembly {
        ptr := mload(data)
    }

    C = mallocM32x32(2, 4); // Allocate memory for matrix.

    copyFromUint256PtrToUnsafe_(ptr, 2, 4, C);
}

function fromArray(uint8[4][4] memory data) pure returns (M32x32 C) {
    uint256 ptr;

    assembly {
        ptr := mload(data)
    }

    C = mallocM32x32(4, 4); // Allocate memory for matrix.

    copyFromUint256PtrToUnsafe_(ptr, 4, 4, C);
}

function fromArray(uint256[2][2] memory data) pure returns (M32x32 C) {
    uint256 ptr;

    assembly {
        ptr := mload(data)
    }

    C = mallocM32x32(2, 2); // Allocate memory for matrix.

    copyFromUint256PtrToUnsafe_(ptr, 2, 2, C);
}

function copyFromUint256PtrToUnsafe_(uint256 ptr, uint256 n, uint256 m, M32x32 C) pure {
    // Loop over all `n * m` elements of 32 bytes.
    uint256 size = n * m * 32;
    // Up until here we can load & parse full words.
    uint256 end = ptr + (size & ~uint256(127));
    // The rest needs to be parsed individually.
    uint256 rest = ptr + size - end;
    // Obtain a pointer to `C`s data location.
    uint256 ptrC = ref(C);

    assembly {
        // Store data bytes length in position `ptr - 32`.
        // This allows to easily retrieve the underlying data as bytes,
        // but unsafely overwrites the word stored in that slot.
        // This might destroy the original data type located at `ptr`.
        mstore(sub(ptr, 32), size)
    }

    while (ptr != end) {
        assembly {
            // Load 4 values from `A` at `ptr`.
            let aX4 := shl(192, mload(ptr))
            aX4 := or(aX4, shl(128, mload(add(32, ptr))))
            aX4 := or(aX4, shl(64, mload(add(64, ptr))))
            aX4 := or(aX4, mload(add(96, ptr)))

            mstore(ptrC, aX4) // Store packed values in `ptrC`.
        }

        // Advance pointers to the next slot.
        ptr = ptr + 128;
        ptrC = ptrC + 32;
    }

    // Parse the last remaining word.
    if (rest != 0) {
        assembly {
            // Mask applies to leftover bits in word.
            let mask := not(shr(mul(rest, 2), not(0)))
            // Load 3 values from `A` at `ptr`.
            let aX4 := shl(192, mload(ptr))
            aX4 := or(aX4, shl(128, and(mload(add(32, ptr)), _UINT64_MAX))) // note: Need to clean bits here.
            aX4 := or(aX4, shl(64, and(mload(add(64, ptr)), _UINT64_MAX))) // note: Need to clean bits here.

            mstore(ptrC, and(aX4, mask)) // Store packed `c` in `ptrC`.
        }
    }
}

function packWordUnsafe(uint256 a, uint256 b, uint256 c, uint256 d) pure returns (uint256 word) {
    word = (a << 192) | (b << 128) | (c << 64) | d;
}
