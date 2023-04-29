// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "./UM256.sol" as __UM256;
import "./N32x32.sol" as __N32x32;

import {
    N32x32,
    ZERO,
    uHALF,
    HALF,
    uONE,
    ONE,
    uTWO,
    TWO,
    uNEG_ONE,
    NEG_ONE,
    uNEG_TWO,
    NEG_TWO,
    uMAX,
    MAX,
    uMIN,
    MIN,
    uHALF_MAX,
    HALF_MAX,
    uHALF_MIN,
    HALF_MIN,
    UINT32_MAX,
    UINT64_MAX,
    MASK_2X4,
    INT64_MIN_X4,
    INT32_MAX,
    INT64_MAX,
    INT64_SIGN,
    INT32_SIGN
} from "./N32x32.sol";

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
    // bytes_,
    copy,
    at,
    atIndex,
    set,
    setUnsafe,
    setIndex,
    fill_,
    add,
    addUnchecked,
    addScalar,
    addScalarTo_,
    addScalarUnchecked,
    addScalarUncheckedTo_,
    mulInt,
    mulScalar,
    mulScalarTo_,
    mulIntUnchecked,
    mulScalarUnchecked,
    mulScalarUncheckedTo_,
    dot,
    dotTransposed,
    abs,
    T,
    transpose,
    transposeNaive,
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
    neg,
    min,
    max,
    minMax,
    map
} for M32x32 global;

error M32x32_TooLarge();
error M32x32_InvalidRange();
error M32x32_IndexOutOfBounds();
error M32x32_InvalidDimensions();
error M32x32_DimensionsNotDivisibleBy4();
error M32x32_IncompatibleDimensions();
error M32x32_Unsupported();

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
    if ((n | m | (ptr >> 40)) > __UM256.MAX_24_BITS) revert M32x32_TooLarge();

    A = M32x32.wrap(
        ptr << 48 // data location
            | m << 24 | n // shape
    );
}

function header(M32x32 A) pure returns (uint256 n, uint256 m, uint256 ptr) {
    n = (M32x32.unwrap(A)) & __UM256.MAX_24_BITS;
    m = (M32x32.unwrap(A) >> 24) & __UM256.MAX_24_BITS;
    ptr = (M32x32.unwrap(A) >> 48) & UINT64_MAX;
}

function shape(M32x32 A) pure returns (uint256 n, uint256 m) {
    n = (M32x32.unwrap(A)) & __UM256.MAX_24_BITS;
    m = (M32x32.unwrap(A) >> 24) & __UM256.MAX_24_BITS;
}

function dim0(M32x32 A) pure returns (uint256 n) {
    n = (M32x32.unwrap(A)) & __UM256.MAX_24_BITS;
}

function dim1(M32x32 A) pure returns (uint256 m) {
    m = (M32x32.unwrap(A) >> 24) & __UM256.MAX_24_BITS;
}

function length(M32x32 A) pure returns (uint256 len) {
    unchecked {
        uint256 n = (M32x32.unwrap(A)) & __UM256.MAX_24_BITS;
        uint256 m = (M32x32.unwrap(A) >> 24) & __UM256.MAX_24_BITS;

        len = n * m;
    }
}

function sizeBytes(M32x32 A) pure returns (uint256 size) {
    unchecked {
        uint256 n = (M32x32.unwrap(A)) & __UM256.MAX_24_BITS;
        uint256 m = (M32x32.unwrap(A) >> 24) & __UM256.MAX_24_BITS;

        size = n * m * 8;
    }
}

function ref(M32x32 A) pure returns (uint256 ptr) {
    ptr = (M32x32.unwrap(A) >> 48) & UINT64_MAX;
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
        uint256 ptr = __UM256.malloc(32 + msize);

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
    fill_(C, ZERO);
}

function ones(uint256 n, uint256 m) pure returns (M32x32 C) {
    // Allocate memory for matrix.
    C = mallocM32x32(n, m);

    // Fill matrix with `1`s.
    fill_(C, ONE);
}

function eye(uint256 n, uint256 m) pure returns (M32x32 C) {
    unchecked {
        // Only allowing square dimensions.
        if (n != m) revert M32x32_InvalidDimensions();

        // Allocate memory for matrix.
        C = mallocM32x32(n, m);

        // Fill matrix with `0`s.
        fill_(C, ZERO);

        // Obtain a pointer to matrix data location.
        // Offset pointer to the left by 3 chunks so that
        // the loaded chunk will be right-aligned.
        uint256 ptr = ref(C) - 24;
        // Spacing in memory between the elements on the diagonal.
        uint256 diagSpacing = 8 + n * 8;
        // Loop over all `n` diagonal elements.
        uint256 end = ptr + n * diagSpacing;

        if (ptr != end) {
            assembly {
                let preserveWord := and(mload(ptr), not(UINT64_MAX))

                mstore(ptr, or(uONE, preserveWord)) // Store `1` at `ptr`, preserve existing word.
            }

            ptr = ptr + diagSpacing; // Advance pointer to the next slot in the diagonal.
        }

        while (ptr != end) {
            assembly {
                mstore(ptr, uONE) // Store `1` at `ptr`.
            }

            ptr = ptr + diagSpacing; // Advance pointer to the next slot in the diagonal.
        }
    }
}

function range(uint256 end) pure returns (M32x32 C) {
    return range(0, end);
}

uint256 constant ONE_X4 = 0x0000000100000000000000010000000000000001000000000000000100000000;
uint256 constant FOUR_X4 = 0x0000000400000000000000040000000000000004000000000000000400000000;

function range(uint256 start, uint256 end) pure returns (M32x32 C) {
    unchecked {
        // `start <= end` must hold.
        if (start > end) revert M32x32_InvalidRange();

        // Number of elements.
        uint256 m = end - start;

        // Allocate memory for matrix.
        C = mallocM32x32(1, m);

        // Obtain a pointer to matrix data location.
        uint256 ptr = ref(C);

        uint256 size = m * 8;
        // Loop over all `m` elements of 8 bytes.
        uint256 ptrEnd = ptr + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = size & 31;
        // Pack `a` into 4 words.
        uint256 aX4 = packWordUnsafe(start, start + 1, start + 2, start + 3) << 32;

        while (ptr != ptrEnd) {
            assembly {
                mstore(ptr, aX4) // Store packed `a` at current pointer location.
            }

            ptr = ptr + 32; // Advance pointer in strides of 4.
            aX4 = aX4 + FOUR_X4;
        }

        if (rest != 0) {
            assembly {
                // Mask applies to leftover bits in word.
                let mask := not(shr(mul(rest, 8), not(0)))
                let preserveWord := and(mload(ptr), not(mask))

                aX4 := and(aX4, mask) // Mask packed `a` to only contain the relevant bits.
                mstore(ptr, or(aX4, preserveWord)) // Store packed `a` at current pointer location.
            }
        }
    }
}

function reshape(M32x32 A, uint256 nNew, uint256 mNew) pure returns (M32x32 out) {
    unchecked {
        (uint256 n, uint256 m, uint256 data) = header(A);

        if (n * m != nNew * mNew) revert M32x32_InvalidDimensions();

        out = M32x32Header(data, nNew, mNew);
    }
}

/* ------------- indexing ------------- */

function atIndex(M32x32 A, uint256 index) pure returns (N32x32 a) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        if (index >= n * m) revert M32x32_IndexOutOfBounds();

        ptr = ptr + 8 * (index - 3);

        assembly {
            a := and(mload(ptr), UINT64_MAX)
        }
    }
}

function setIndex(M32x32 A, uint256 index, N32x32 value) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        if (index >= n * m) revert M32x32_IndexOutOfBounds();

        ptr = ptr + 8 * (index - 3);

        assembly {
            value := and(value, UINT64_MAX)
            let preserveWord := and(mload(ptr), not(UINT64_MAX))

            mstore(ptr, or(preserveWord, value))
        }
    }
}

function at(M32x32 A, uint256 i, uint256 j) pure returns (N32x32 a) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        if (i >= n || j >= m) revert M32x32_IndexOutOfBounds();

        ptr = ptr + 8 * (i * m + j - 3);

        assembly {
            a := and(mload(ptr), UINT64_MAX)
        }
    }
}

function set(M32x32 A, uint256 i, uint256 j, N32x32 value) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        if (i >= n || j >= m) revert M32x32_IndexOutOfBounds();

        ptr = ptr + 8 * (i * m + j - 3);

        assembly {
            value := and(value, UINT64_MAX)
            let preserveWord := and(mload(ptr), not(UINT64_MAX))

            mstore(ptr, or(preserveWord, value))
        }
    }
}

function setUnsafe(M32x32 A, uint256 i, uint256 j, N32x32 value) pure {
    unchecked {
        (, uint256 m, uint256 ptr) = header(A);

        ptr = ptr + 8 * (uint256(i) * m + uint256(j) - 3);

        assembly {
            let preserveWord := and(mload(ptr), not(UINT64_MAX))

            mstore(ptr, or(value, preserveWord))
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
        // Up until here we can load & parse full words (4 elements).
        uint256 endA = ptrA + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = size & 31;
        // Obtain a pointer to `C`s data location.
        uint256 ptrC = ref(C);

        while (ptrA != endA) {
            assembly {
                let a := mload(ptrA) // Load 4 values from `A` at `ptrA`.
                let b := mload(ptrB) // Load 4 values from `B` at `ptrB`.

                // Add packed values together.
                let c := and(add(and(a, MASK_2X4), and(b, MASK_2X4)), MASK_2X4)
                c := or(c, and(add(and(a, not(MASK_2X4)), and(b, not(MASK_2X4))), not(MASK_2X4)))

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
                let a := and(mload(ptrA), mask) // Load packed values from `A` at `ptrA`.
                let b := and(mload(ptrB), mask) // Load packed values from `B` at `ptrB`.

                // Add packed values together.
                let c := and(add(and(a, MASK_2X4), and(b, MASK_2X4)), MASK_2X4)
                c := or(c, and(add(and(a, not(MASK_2X4)), and(b, not(MASK_2X4))), not(MASK_2X4)))

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
        // Up until here we can load & parse full words (4 elements).
        uint256 endA = ptrA + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = size & 31;
        // Obtain a pointer to `C`s data location.
        uint256 ptrC = ref(C);

        // Keep track of over/underflows.
        uint256 overflow;

        // Loop over 32 byte words.
        while (ptrA != endA) {
            assembly {
                let a := mload(ptrA) // Load 4 values from `A` at `ptrA`.
                let b := mload(ptrB) // Load 4 values from `B` at `ptrB`.

                // Add packed values together.
                let c := and(add(and(a, MASK_2X4), and(b, MASK_2X4)), MASK_2X4)
                c := or(c, and(add(and(a, not(MASK_2X4)), and(b, not(MASK_2X4))), not(MASK_2X4)))

                mstore(ptrC, c) // Store packed values in `ptrC`.

                // Overflow when signs of `a` and `s` are equal, but differ from `c`.
                overflow := or(overflow, and(and(not(xor(a, b)), xor(a, c)), INT64_MIN_X4))
            }

            // Advance pointers to the next slot.
            ptrA = ptrA + 32;
            ptrB = ptrB + 32;
            ptrC = ptrC + 32;
        }

        // Parse the last remaining word.
        if (rest != 0) {
            assembly {
                let mask := not(shr(mul(rest, 8), not(0)))
                let a := and(mload(ptrA), mask) // Load packed values from `A` at `ptrA`.
                let b := and(mload(ptrB), mask) // Load packed values from `B` at `ptrB`.

                // Add packed values together.
                let c := and(add(and(a, MASK_2X4), and(b, MASK_2X4)), MASK_2X4)
                c := or(c, and(add(and(a, not(MASK_2X4)), and(b, not(MASK_2X4))), not(MASK_2X4)))

                // Overflow when signs of `a` and `s` are equal, but differ from `c`.
                overflow := or(overflow, and(and(not(xor(a, b)), xor(a, c)), INT64_MIN_X4))

                mstore(ptrC, c) // Store packed `c` in `ptrC`.
            }
        }

        // if (overflow != 0) revert __N32x32.N32x32_Overflow();
        if (overflow > UINT64_MAX) revert __N32x32.N32x32_Overflow();
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
        (uint256 nA, uint256 mA, uint256 ptrA) = header(A);
        (uint256 nB, uint256 mB, uint256 ptrB) = header(B);

        if (mA != nB) revert M32x32_IncompatibleDimensions();

        C = mallocM32x32(nA, mB);

        uint256 ptrCij = ref(C);

        uint256 rowSizeA = 8 * mA;
        uint256 rowSizeB = 8 * mB;

        uint256 ptrARowEnd = ptrA + 8 * nA * mA;
        uint256 ptrARow = ptrA; // Updates by row size of `A` in i-loop.

        uint256 ptrBColEnd = ptrB + (rowSizeB & ~uint256(31));
        uint256 ptrBjRest = rowSizeB & 31;
        uint256 ptrBCol;

        // Loop over `A`s `i` indices (rows).
        while (ptrARow != ptrARowEnd) {
            // i-loop start.

            ptrBCol = ptrB;

            // Loop over `B`s `j` indices (cols).
            while (ptrBCol != ptrBColEnd) {
                // j-loop start.

                uint256 ptrBkj = ptrBCol;
                uint256 ptrAik = ptrARow;
                // End inner loop after one row of `A`.
                // Up until here we can load & parse full words (4 elements).
                uint256 ptrAEnd = ptrARow + (rowSizeA & ~uint256(31));
                // The rest needs to be parsed individually.
                uint256 ptrARest = rowSizeA & 31;

                // Perform the dot product on the current
                // row vector `Ai` and the column vector `Bj`.
                // Store the result in `c`.
                uint256 cX4;

                // Loop over `A`s cols and `B`s rows in strides of 4.
                while (ptrAik != ptrAEnd) {
                    // k-loop start.

                    assembly {
                        let aX4 := mload(ptrAik) // Load packed A[i:i+4,k].

                        let b1X4 := mload(ptrBkj) // Load packed B[k+0,j:j+4].
                        ptrBkj := add(ptrBkj, rowSizeB) // Advance to the next row ↓ of `B`.
                        let b2X4 := mload(ptrBkj) // Load packed B[k+1,j:j+4].
                        ptrBkj := add(ptrBkj, rowSizeB) // Advance to the next row ↓ of `B`.
                        let b3X4 := mload(ptrBkj) // Load packed B[k+2,j:j+4].
                        ptrBkj := add(ptrBkj, rowSizeB) // Advance to the next row ↓ of `B`.
                        let b4X4 := mload(ptrBkj) // Load packed B[k+3,j:j+4].
                        ptrBkj := add(ptrBkj, rowSizeB) // Advance to the next row ↓ of `B`.

                        cX4 := add(cX4, mul(shr(192, aX4), b1X4))
                        cX4 := add(cX4, mul(and(shr(128, aX4), UINT64_MAX), b2X4))
                        cX4 := add(cX4, mul(and(shr(64, aX4), UINT64_MAX), b3X4))
                        cX4 := add(cX4, mul(and(aX4, UINT64_MAX), b4X4))
                    }

                    ptrAik = ptrAik + 32; // Advance to the next column → of `A` in strides of 4.
                }

                // Parse the last remaining word.
                if (ptrARest != 0) {
                    assembly {
                        // Mask applies to leftover bits in word.
                        let mask := not(shr(mul(ptrARest, 8), not(0)))
                        let aX4 := and(mload(ptrAik), mask) // Load packed values from `A` at `ptrA`.

                        let b1X4 := mload(ptrBkj) // Load packed B[k+0,j:j+4].
                        ptrBkj := add(ptrBkj, rowSizeB) // Advance to the next row ↓ of `B`.
                        let b2X4 := mload(ptrBkj) // Load packed B[k+1,j:j+4].
                        ptrBkj := add(ptrBkj, rowSizeB) // Advance to the next row ↓ of `B`.
                        let b3X4 := mload(ptrBkj) // Load packed B[k+2,j:j+4].
                        ptrBkj := add(ptrBkj, rowSizeB) // Advance to the next row ↓ of `B`.

                        cX4 := add(cX4, mul(shr(192, aX4), and(b1X4, mask)))
                        cX4 := add(cX4, mul(and(shr(128, aX4), UINT64_MAX), and(b2X4, mask)))
                        cX4 := add(cX4, mul(and(shr(64, aX4), UINT64_MAX), and(b3X4, mask)))
                    }
                }

                assembly {
                    mstore(ptrCij, cX4) // Store the packed result in C[i:i+4,j].
                }

                ptrCij = ptrCij + 32; // Advance to the next element of `C` in strides of 4.
                ptrBCol = ptrBCol + 32; // Advance to the next column → of `B` in strides of 4.
            }

            if (ptrBjRest != 0) {
                // Repeat the while-loop and apply masking.
                uint256 maskBj;
                assembly {
                    // Mask applies to leftover bits in word.
                    maskBj := not(shr(mul(ptrBjRest, 8), not(0)))
                }

                uint256 ptrBkj = ptrBCol;
                uint256 ptrAik = ptrARow;
                // End inner loop after one row of `A`.
                // Up until here we can load & parse full words (4 elements).
                uint256 ptrAEnd = ptrARow + (rowSizeA & ~uint256(31));
                // // The rest needs to be parsed individually.
                // uint256 ptrARest = rowSizeA & 31;

                // Perform the dot product on the current
                // row vector `Ai` and the column vector `Bj`.
                // Store the result in `c`.
                uint256 cX4;

                // Loop over `A`s cols and `B`s rows in strides of 4.
                while (ptrAik != ptrAEnd) {
                    // k-loop start.

                    assembly {
                        let aX4 := mload(ptrAik) // Load packed A[i,k].

                        let b1X4 := and(mload(ptrBkj), maskBj) // Load packed B[k,j].
                        ptrBkj := add(ptrBkj, rowSizeB) // Advance to the next row ↓ of `B`.
                        let b2X4 := and(mload(ptrBkj), maskBj) // Load packed B[k,j].
                        ptrBkj := add(ptrBkj, rowSizeB) // Advance to the next row ↓ of `B`.
                        let b3X4 := and(mload(ptrBkj), maskBj) // Load packed B[k,j].
                        ptrBkj := add(ptrBkj, rowSizeB) // Advance to the next row ↓ of `B`.
                        let b4X4 := and(mload(ptrBkj), maskBj) // Load packed B[k,j].
                        ptrBkj := add(ptrBkj, rowSizeB) // Advance to the next row ↓ of `B`.

                        cX4 := add(cX4, mul(shr(192, aX4), b1X4))
                        cX4 := add(cX4, mul(and(shr(128, aX4), UINT64_MAX), b2X4))
                        cX4 := add(cX4, mul(and(shr(64, aX4), UINT64_MAX), b3X4))
                        cX4 := add(cX4, mul(and(aX4, UINT64_MAX), b4X4))
                    }

                    ptrAik = ptrAik + 32; // Advance to the next column → of `A` in strides of 4.
                }

                // Parse the last remaining word.
                if (rowSizeA & 31 != 0) {
                    assembly {
                        // Mask applies to leftover bits in word.
                        let mask := not(shr(mul(and(rowSizeA, 31), 8), not(0)))
                        let aX4 := and(mload(ptrAik), mask) // Load packed values from `A` at `ptrA`.

                        let b1X4 := and(mload(ptrBkj), maskBj) // Load packed B[k,j].
                        ptrBkj := add(ptrBkj, rowSizeB) // Advance to the next row ↓ of `B`.
                        let b2X4 := and(mload(ptrBkj), maskBj) // Load packed B[k,j].
                        ptrBkj := add(ptrBkj, rowSizeB) // Advance to the next row ↓ of `B`.
                        let b3X4 := and(mload(ptrBkj), maskBj) // Load packed B[k,j].

                        cX4 := add(cX4, mul(shr(192, aX4), and(b1X4, mask)))
                        cX4 := add(cX4, mul(and(shr(128, aX4), UINT64_MAX), and(b2X4, mask)))
                        cX4 := add(cX4, mul(and(shr(64, aX4), UINT64_MAX), and(b3X4, mask)))
                    }
                }

                assembly {
                    mstore(ptrCij, cX4) // Store the packed result in C[i,j].
                }

                ptrCij = ptrCij + (ptrBjRest & 31); // Advance to the next row ↓ of `C`.
            }

            ptrARow = ptrARow + rowSizeA; // Advance to the next row ↓ of `A`.
        }
    }
}

/// @dev Computes `C_ij = A_ik B_jk`
function dotTransposedX4(M32x32 A, M32x32 B) pure returns (M32x32 C) {
    unchecked {
        (uint256 nA, uint256 mA, uint256 ptrA) = header(A);
        (uint256 nB, uint256 mB, uint256 ptrB) = header(B);

        if (mA != mB) revert M32x32_IncompatibleDimensions();

        C = mallocM32x32(nA, nB);

        // Offset pointer by 3 (of 4) 8 byte chunks.
        // This way the loaded values will be right-aligned.
        uint256 ptrCij = ref(C);

        uint256 rowSizeA = 8 * mA;
        uint256 rowSizeB = 8 * mB;

        uint256 ptrARowEnd = ptrA + 8 * nA * mA;
        uint256 ptrARow = ptrA; // Updates by row size of `A` in i-loop.

        // // Up until here we can load & parse full words (4 elements).
        // uint256 ptrBColEnd = ptrB + (rowSizeB & ~uint256(31));
        // // The rest needs to be parsed individually.
        // uint256 ptrBjRest = rowSizeB & 31;
        uint256 ptrBColEnd = ptrB + 8 * nB * mB;
        uint256 ptrBCol;

        // Loop over `A`s `i` indices (rows).
        while (ptrARow != ptrARowEnd) {
            // i-loop start.

            ptrBCol = ptrB;

            // Loop over `B`s `j` indices (rows).
            while (ptrBCol != ptrBColEnd) {
                // j-loop start.

                uint256 l;
                // Perform the dot product on the current
                // row vector `Ai` and the row vector `Bj`.
                // Store the result in `c`.
                uint256 cX4;

                while (true) {
                    uint256 ptrBjk = ptrBCol;
                    uint256 ptrAik = ptrARow;
                    // End inner loop after one row of `A`.
                    // Up until here we can load & parse full words (4 elements).
                    uint256 ptrAEnd = ptrARow + (rowSizeA & ~uint256(31));
                    // The rest needs to be parsed individually.
                    uint256 ptrARest = rowSizeA & 31;

                    // Loop over `A`s cols and `B`s cols in strides of 4.
                    while (ptrAik != ptrAEnd) {
                        // k-loop start.

                        assembly {
                            let aX4 := mload(ptrAik) // Load packed A[i,k].
                            let bX4 := mload(ptrBjk) // Load packed B[j,k].

                            cX4 := add(cX4, mul(and(aX4, UINT64_MAX), and(bX4, UINT64_MAX)))
                            cX4 := add(cX4, mul(and(shr(64, aX4), UINT64_MAX), and(shr(64, bX4), UINT64_MAX)))
                            cX4 := add(cX4, mul(and(shr(128, aX4), UINT64_MAX), and(shr(128, bX4), UINT64_MAX)))
                            cX4 := add(cX4, mul(shr(192, aX4), shr(192, bX4)))
                        }

                        ptrAik = ptrAik + 32; // Advance to the next column → of `A` in strides of 4.
                        ptrBjk = ptrBjk + 32; // Advance to the next column → of `B` in strides of 4.
                    }

                    // Parse the last remaining word.
                    if (ptrARest != 0) {
                        assembly {
                            // Mask applies to leftover bits in word.
                            let mask := not(shr(mul(ptrARest, 8), not(0)))
                            let aX4 := and(mload(ptrAik), mask) // Load packed values from `A` at `ptrA`.
                            let bX4 := and(mload(ptrBjk), mask) // Load packed values from `B` at `ptrB`.

                            cX4 := add(cX4, mul(and(shr(64, aX4), UINT64_MAX), and(shr(64, bX4), UINT64_MAX)))
                            cX4 := add(cX4, mul(and(shr(128, aX4), UINT64_MAX), and(shr(128, bX4), UINT64_MAX)))
                            cX4 := add(cX4, mul(shr(192, aX4), shr(192, bX4)))
                        }
                    }

                    ptrBCol = ptrBCol + rowSizeB; // Advance to the next row ↓ of `B`.

                    if (l == 3) break;

                    l = l + 1;
                    cX4 = cX4 << 64;
                }

                assembly {
                    // // Preserve the previous data in memory.
                    // let word := and(mload(ptrCij), not(UINT64_MAX))

                    mstore(ptrCij, cX4) // Store the result in C[i,j].
                }

                ptrCij = ptrCij + 32; // Advance to the next element of `C` in strides of 4.
            }

            ptrARow = ptrARow + rowSizeA; // Advance to the next row ↓ of `A`.
        }
    }
}

function dotX4(M32x32 A, M32x32 B) pure returns (M32x32 C) {
    unchecked {
        (uint256 nA, uint256 mA, uint256 ptrA) = header(A);
        (uint256 nB, uint256 mB, uint256 ptrB) = header(B);

        if (mA != nB) revert M32x32_IncompatibleDimensions();
        if ((mB | mA) & 3 != 0) revert M32x32_DimensionsNotDivisibleBy4();

        C = mallocM32x32(nA, mB);

        uint256 ptrCij = ref(C);

        uint256 rowSizeA = 8 * mA;
        uint256 rowSizeB = 8 * mB;

        uint256 ptrARowEnd = ptrA + 8 * nA * mA;
        uint256 ptrARow = ptrA; // Updates by row size of `A` in i-loop.

        uint256 ptrBColEnd = ptrB + rowSizeB;
        uint256 ptrBCol;

        // Loop over `A`s `i` indices (rows).
        while (ptrARow != ptrARowEnd) {
            // i-loop start.

            ptrBCol = ptrB;

            // Loop over `B`s `j` indices (cols).
            while (ptrBCol != ptrBColEnd) {
                // j-loop start.

                uint256 ptrBkj = ptrBCol;
                uint256 ptrAik = ptrARow;
                // End inner loop after one row of `A`.
                uint256 ptrAEnd = ptrARow + rowSizeA;

                // Perform the dot product on the current
                // row vector `Ai` and the column vector `Bj`.
                // Store the result in packed `c`.
                uint256 cX4;

                // Loop over `A`s cols and `B`s rows in strides of 4.
                while (ptrAik != ptrAEnd) {
                    // k-loop start.

                    assembly {
                        let aX4 := mload(ptrAik) // Load packed A[i,k].

                        let b1X4 := mload(ptrBkj) // Load packed B[k,j].
                        ptrBkj := add(ptrBkj, rowSizeB) // Advance to the next row ↓ of `B`.
                        let b2X4 := mload(ptrBkj) // Load packed B[k,j].
                        ptrBkj := add(ptrBkj, rowSizeB) // Advance to the next row ↓ of `B`.
                        let b3X4 := mload(ptrBkj) // Load packed B[k,j].
                        ptrBkj := add(ptrBkj, rowSizeB) // Advance to the next row ↓ of `B`.
                        let b4X4 := mload(ptrBkj) // Load packed B[k,j].
                        ptrBkj := add(ptrBkj, rowSizeB) // Advance to the next row ↓ of `B`.

                        cX4 := add(cX4, mul(shr(192, aX4), b1X4))
                        cX4 := add(cX4, mul(and(shr(128, aX4), UINT64_MAX), b2X4))
                        cX4 := add(cX4, mul(and(shr(64, aX4), UINT64_MAX), b3X4))
                        cX4 := add(cX4, mul(and(aX4, UINT64_MAX), b4X4))
                    }

                    ptrAik = ptrAik + 32; // Advance to the next column → of `A` in strides of 4.
                }

                assembly {
                    mstore(ptrCij, cX4) // Store the packed result in C[i,j].
                }

                ptrCij = ptrCij + 32; // Advance to the next element of `C` in strides of 4.
                ptrBCol = ptrBCol + 32; // Advance to the next column → of `B` in strides of 4.
            }

            ptrARow = ptrARow + rowSizeA; // Advance to the next row ↓ of `A`.
        }
    }
}

/// @dev Computes `C_ij = A_ik B_jk`
function dotTransposed(M32x32 A, M32x32 B) pure returns (M32x32 C) {
    unchecked {
        (uint256 nA, uint256 mA, uint256 refA) = header(A);
        (uint256 nB, uint256 mB, uint256 refB) = header(B);

        if (mA != mB) revert M32x32_IncompatibleDimensions();

        C = mallocM32x32(nA, nB);

        // Offset pointer by 3 (of 4) 8 byte chunks.
        // This way the loaded values will be right-aligned.
        uint256 ptrC = ref(C) - 24;

        uint256 rowSizeA = 8 * mA;
        uint256 rowSizeB = 8 * mB;

        uint256 ptrARowEnd = refA + 8 * nA * mA;
        uint256 ptrARow = refA; // Updates by row size of `A` in i-loop.

        uint256 ptrBRowEnd = refB + 8 * nB * mB;
        uint256 ptrBRow;

        // Keep track of overflow
        uint256 overflow;

        // Loop over `A`s rows ↓.
        while (ptrARow != ptrARowEnd) {
            ptrBRow = refB;

            // Loop over `B`s rows ↓.
            while (ptrBRow != ptrBRowEnd) {
                uint256 ptrA = ptrARow;
                uint256 ptrB = ptrBRow;
                // End inner loop after one row of `A`.
                // Up until here we can load & parse full words (4 elements).
                uint256 ptrAEnd = ptrARow + (rowSizeA & ~uint256(31));
                // The rest needs to be parsed individually.
                uint256 ptrARest = rowSizeA & 31;

                // Perform the dot product on the current
                // row vector in `A` and the row vector `B`.
                // Store the result in `c`.
                uint256 c;

                // Loop over `A`s cols → and `B`s cols → in strides of 4.
                while (ptrA != ptrAEnd) {
                    assembly {
                        let aX4 := mload(ptrA) // Load packed A[i,k].
                        let bX4 := mload(ptrB) // Load packed B[j,k].

                        c := add(c, mul(signextend(7, aX4), signextend(7, bX4)))
                        c := add(c, mul(signextend(7, shr(64, aX4)), signextend(7, shr(64, bX4))))
                        c := add(c, mul(signextend(7, shr(128, aX4)), signextend(7, shr(128, bX4))))
                        c := add(c, mul(sar(192, aX4), sar(192, bX4)))
                    }

                    ptrA = ptrA + 32; // Advance to the next column → of `A` in strides of 4.
                    ptrB = ptrB + 32; // Advance to the next column → of `B` in strides of 4.
                }

                // Parse the last remaining word.
                if (ptrARest != 0) {
                    assembly {
                        // Mask applies to leftover bits in word.
                        let mask := not(shr(mul(ptrARest, 8), not(0)))
                        let aX4 := and(mload(ptrA), mask) // Load packed values from `A` at `ptrA`.
                        let bX4 := and(mload(ptrB), mask) // Load packed values from `B` at `ptrB`.

                        c := add(c, mul(signextend(7, shr(64, aX4)), signextend(7, shr(64, bX4))))
                        c := add(c, mul(signextend(7, shr(128, aX4)), signextend(7, shr(128, bX4))))
                        c := add(c, mul(sar(192, aX4), sar(192, bX4)))
                    }
                }

                assembly {
                    c := sar(32, c)
                    overflow := or(overflow, add(c, INT64_SIGN))
                }

                assembly {
                    // Preserve the previous data in memory.
                    let word := and(mload(ptrC), not(UINT64_MAX))

                    mstore(ptrC, or(word, c)) // Store the result in C[i,j].
                }

                ptrC = ptrC + 8; // Advance to the next element of `C`.
                ptrBRow = ptrBRow + rowSizeB; // Advance to the next row ↓ of `B`.
            }

            ptrARow = ptrARow + rowSizeA; // Advance to the next row ↓ of `A`.
        }

        if (overflow > UINT64_MAX) revert __N32x32.N32x32_Overflow();
    }
}

// /// @dev Computes `C_ij = A_ik B_jk`
// function dotTransposedX4(M32x32 A, M32x32 B) pure returns (M32x32 C) {
//     unchecked {
//         (uint256 nA, uint256 mA, uint256 ptrA) = header(A);
//         (uint256 nB, uint256 mB, uint256 ptrB) = header(B);

//         if (mA != mB) revert M32x32_IncompatibleDimensions();

//         C = mallocM32x32(nA, nB);

//         // Offset pointer by 3 (of 4) 8 byte chunks.
//         // This way the loaded values will be right-aligned.
//         uint256 ptrCij = ref(C);

//         uint256 rowSizeA = 8 * mA;
//         uint256 rowSizeB = 8 * mB;

//         uint256 ptrARowEnd = ptrA + 8 * nA * mA;
//         uint256 ptrARow = ptrA; // Updates by row size of `A` in i-loop.

//         // // Up until here we can load & parse full words (4 elements).
//         // uint256 ptrBRowEnd = ptrB + (rowSizeB & ~uint256(31));
//         // // The rest needs to be parsed individually.
//         // uint256 ptrBjRest = rowSizeB & 31;
//         uint256 ptrBRowEnd = ptrB + 8 * nB * mB;
//         uint256 ptrBRow;

//         // Loop over `A`s `i` indices (rows).
//         while (ptrARow != ptrARowEnd) {
//             // i-loop start.

//             ptrBRow = ptrB;

//             // Loop over `B`s `j` indices (rows).
//             while (ptrBRow != ptrBRowEnd) {
//                 // j-loop start.

//                 uint256 l;
//                 // Perform the dot product on the current
//                 // row vector `Ai` and the row vector `Bj`.
//                 // Store the result in `c`.
//                 uint256 cX4;

//                 while (true) {
//                     uint256 ptrBjk = ptrBRow;
//                     uint256 ptrAik = ptrARow;
//                     // End inner loop after one row of `A`.
//                     // Up until here we can load & parse full words (4 elements).
//                     uint256 ptrAEnd = ptrARow + (rowSizeA & ~uint256(31));
//                     // The rest needs to be parsed individually.
//                     uint256 ptrARest = rowSizeA & 31;

//                     // Loop over `A`s cols and `B`s cols in strides of 4.
//                     while (ptrAik != ptrAEnd) {
//                         // k-loop start.

//                         assembly {
//                             let aX4 := mload(ptrAik) // Load packed A[i,k].
//                             let bX4 := mload(ptrBjk) // Load packed B[j,k].

//                             cX4 := add(cX4, mul(and(aX4, UINT64_MAX), and(bX4, UINT64_MAX)))
//                             cX4 := add(cX4, mul(and(shr(64, aX4), UINT64_MAX), and(shr(64, bX4), UINT64_MAX)))
//                             cX4 := add(cX4, mul(and(shr(128, aX4), UINT64_MAX), and(shr(128, bX4), UINT64_MAX)))
//                             cX4 := add(cX4, mul(shr(192, aX4), shr(192, bX4)))
//                         }

//                         ptrAik = ptrAik + 32; // Advance to the next column → of `A` in strides of 4.
//                         ptrBjk = ptrBjk + 32; // Advance to the next column → of `B` in strides of 4.
//                     }

//                     // Parse the last remaining word.
//                     if (ptrARest != 0) {
//                         assembly {
//                             // Mask applies to leftover bits in word.
//                             let mask := not(shr(mul(ptrARest, 8), not(0)))
//                             let aX4 := and(mload(ptrAik), mask) // Load packed values from `A` at `ptrA`.
//                             let bX4 := and(mload(ptrBjk), mask) // Load packed values from `B` at `ptrB`.

//                             cX4 := add(cX4, mul(and(shr(64, aX4), UINT64_MAX), and(shr(64, bX4), UINT64_MAX)))
//                             cX4 := add(cX4, mul(and(shr(128, aX4), UINT64_MAX), and(shr(128, bX4), UINT64_MAX)))
//                             cX4 := add(cX4, mul(shr(192, aX4), shr(192, bX4)))
//                         }
//                     }

//                     ptrBRow = ptrBRow + rowSizeB; // Advance to the next row ↓ of `B`.

//                     if (l == 3) break;

//                     l = l + 1;
//                     cX4 = cX4 << 64;
//                 }

//                 assembly {
//                     // // Preserve the previous data in memory.
//                     // let word := and(mload(ptrCij), not(UINT64_MAX))

//                     mstore(ptrCij, cX4) // Store the result in C[i,j].
//                 }

//                 ptrCij = ptrCij + 32; // Advance to the next element of `C` in strides of 4.
//             }

//             ptrARow = ptrARow + rowSizeA; // Advance to the next row ↓ of `A`.
//         }
//     }
// }

function eqAll(M32x32 A, M32x32 B) pure returns (bool equals) {
    unchecked {
        if (M32x32.unwrap(A) == M32x32.unwrap(B)) return true;

        (uint256 nA, uint256 mA, uint256 ptrA) = header(A);
        (uint256 nB, uint256 mB, uint256 ptrB) = header(B);

        equals = nA == nB && mA == mB;

        // Loop over all `n * m` elements of 8 bytes.
        uint256 size = nA * mA * 8;
        // Up until here we can load & parse full words (4 elements).
        uint256 endA = ptrA + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = size & 31;

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
            uint256 a = (wordA >> ((32 - rest) * 8)) & UINT64_MAX;
            uint256 b = (wordB >> ((32 - rest) * 8)) & UINT64_MAX;

            equals = equals && (a == b);
            rest = rest - 8;
        }
    }
}

/* ------------- Mat x scalar operators ------------- */

function addScalarUnchecked(M32x32 A, N32x32 s) pure returns (M32x32 C) {
    (uint256 n, uint256 m) = A.shape();

    // Allocate new matrix of the same dimensions.
    C = mallocM32x32(n, m);

    // Add scalar `s` to `A`, store result in `C`.
    addScalarUncheckedTo_(A, s, C);
}

function addScalar(M32x32 A, N32x32 s) pure returns (M32x32 C) {
    (uint256 n, uint256 m) = A.shape();

    // Allocate new matrix of the same dimensions.
    C = mallocM32x32(n, m);

    // Add scalar `s` to `A`, store result in `C`.
    addScalarTo_(A, s, C);
}

function addScalarUncheckedTo_(M32x32 A, N32x32 s, M32x32 C) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrA) = header(A);

        // Loop over all `n * m` elements of 8 bytes.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words (4 elements).
        uint256 endA = ptrA + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = size & 31;
        // Pack `s` in one word for efficiency.
        uint256 sX4 = packWordUnsafe(s, s, s, s);
        // Obtain a pointer to `C`s data location.
        uint256 ptrC = ref(C);

        // Loop over 32 byte words.
        while (ptrA != endA) {
            assembly {
                let a := mload(ptrA) // Load 4 values from `A` at `ptrA`.
                // Add packed values together.
                let c := and(add(and(a, MASK_2X4), and(sX4, MASK_2X4)), MASK_2X4)
                c := or(c, and(add(and(a, not(MASK_2X4)), and(sX4, not(MASK_2X4))), not(MASK_2X4)))

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
                let a := and(mload(ptrA), mask)
                // Add packed values together.
                let c := and(add(and(a, MASK_2X4), and(sX4, MASK_2X4)), MASK_2X4)
                c := or(c, and(add(and(a, not(MASK_2X4)), and(sX4, not(MASK_2X4))), not(MASK_2X4)))

                mstore(ptrC, c) // Store packed `c` in `ptrC`.
            }
        }
    }
}

function addScalarTo_(M32x32 A, N32x32 s, M32x32 C) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrA) = header(A);

        // Loop over all `n * m` elements of 8 bytes.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words (4 elements).
        uint256 endA = ptrA + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = size & 31;
        // Pack `s` in one word for efficiency.
        uint256 sX4 = packWordUnsafe(s, s, s, s);
        // Obtain a pointer to `C`s data location.
        uint256 ptrC = ref(C);

        // Keep track of over/underflows.
        uint256 overflow;

        // Loop over 32 byte words.
        while (ptrA != endA) {
            assembly {
                let a := mload(ptrA) // Load 4 values from `A` at `ptrA`.

                // Add packed values together.
                let c := and(add(and(a, MASK_2X4), and(sX4, MASK_2X4)), MASK_2X4)
                c := or(c, and(add(and(a, not(MASK_2X4)), and(sX4, not(MASK_2X4))), not(MASK_2X4)))

                // Overflow when signs of `a` and `s` are equal, but differ from `c`.
                overflow := or(overflow, and(and(not(xor(a, sX4)), xor(a, c)), INT64_MIN_X4))

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
                // Load packed values from `A` at `ptrA` and mask.
                let a := and(mload(ptrA), mask)
                sX4 := and(sX4, mask)

                // Add packed values together.
                let c := and(add(and(a, MASK_2X4), and(sX4, MASK_2X4)), MASK_2X4)
                c := or(c, and(add(and(a, not(MASK_2X4)), and(sX4, not(MASK_2X4))), not(MASK_2X4)))

                mstore(ptrC, c) // Store packed `c` in `ptrC`.

                // Overflow when signs of `a` and `s` are equal, but differ from `c`.
                overflow := or(overflow, and(and(not(xor(a, sX4)), xor(a, c)), INT64_MIN_X4))
            }
        }

        if (overflow != 0) revert __N32x32.N32x32_Overflow();
    }
}

function mulIntUnchecked(M32x32 A, int256 s) pure returns (M32x32 C) {
    (uint256 n, uint256 m) = A.shape();

    // Allocate new matrix of the same dimensions.
    C = mallocM32x32(n, m);

    // Multiply `A` with scalar `s`, store result in `C`.
    mulScalarUncheckedTo_(A, N32x32.wrap(int64(s)), C);
}

function mulInt(M32x32 A, int256 s) pure returns (M32x32 C) {
    (uint256 n, uint256 m) = A.shape();

    // Allocate new matrix of the same dimensions.
    C = mallocM32x32(n, m);

    // Multiply `A` with scalar `s`, store result in `C`.
    mulScalarTo_(A, __N32x32.N32x32FromInt(s), C);
}

function mulScalarUnchecked(M32x32 A, N32x32 s) pure returns (M32x32 C) {
    (uint256 n, uint256 m) = A.shape();

    // Allocate new matrix of the same dimensions.
    C = mallocM32x32(n, m);

    // Multiply `A` with scalar `s`, store result in `C`.
    mulScalarUncheckedTo_(A, s, C);
}

function mulScalar(M32x32 A, N32x32 s) pure returns (M32x32 C) {
    (uint256 n, uint256 m) = A.shape();

    // Allocate new matrix of the same dimensions.
    C = mallocM32x32(n, m);

    // Multiply `A` with scalar `s`, store result in `C`.
    mulScalarTo_(A, s, C);
}

function mulScalarUncheckedTo_(M32x32 A, N32x32 s, M32x32 C) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrA) = header(A);

        // Loop over all `n * m` elements of 8 bytes.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words (4 elements).
        uint256 endA = ptrA + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = size & 31;
        // Obtain a pointer to `C`s data location.
        uint256 ptrC = ref(C);

        // Loop over 32 byte words.
        while (ptrA != endA) {
            assembly {
                let a := mload(ptrA) // Load 4 values from `A` at `ptrA`.

                // Multiply packed values together.
                let c := sar(32, mul(signextend(7, a), s))
                let cX4 := and(c, UINT64_MAX)

                c := sar(32, mul(signextend(7, shr(64, a)), s))
                cX4 := or(cX4, shl(64, and(c, UINT64_MAX)))

                c := sar(32, mul(signextend(7, shr(128, a)), s))
                cX4 := or(cX4, shl(128, and(c, UINT64_MAX)))

                c := sar(32, mul(sar(192, a), s))
                cX4 := or(cX4, shl(192, and(c, UINT64_MAX)))

                mstore(ptrC, cX4) // Store packed `c` in `ptrC`.
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

                // Multiply packed `a` with `s` and keep track of carry.
                let c := sar(32, mul(signextend(7, a), s))
                let cX4 := and(c, UINT64_MAX)

                c := sar(32, mul(signextend(7, shr(64, a)), s))
                cX4 := or(cX4, shl(64, and(c, UINT64_MAX)))

                c := sar(32, mul(signextend(7, shr(128, a)), s))
                cX4 := or(cX4, shl(128, and(c, UINT64_MAX)))

                c := sar(32, mul(sar(192, a), s))
                cX4 := or(cX4, shl(192, and(c, UINT64_MAX)))

                mstore(ptrC, cX4) // Store packed `cX4` in `ptrC`.
            }
        }
    }
}

function mulScalarTo_(M32x32 A, N32x32 s, M32x32 C) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrA) = header(A);

        // Loop over all `n * m` elements of 8 bytes.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words (4 elements).
        uint256 endA = ptrA + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = size & 31;
        // Obtain a pointer to `C`s data location.
        uint256 ptrC = ref(C);
        // Keep track of carry bits.
        uint256 carry;

        // Loop over 32 byte words.
        while (ptrA != endA) {
            assembly {
                let a := mload(ptrA) // Load 4 values from `A` at `ptrA`.

                // Multiply packed `a` with `s` and keep track of carry.
                let c := sar(32, mul(signextend(7, a), s))
                carry := or(carry, add(c, INT64_SIGN))
                let cX4 := and(c, UINT64_MAX)

                c := sar(32, mul(signextend(7, shr(64, a)), s))
                carry := or(carry, add(c, INT64_SIGN))
                cX4 := or(cX4, shl(64, and(c, UINT64_MAX)))

                c := sar(32, mul(signextend(7, shr(128, a)), s))
                carry := or(carry, add(c, INT64_SIGN))
                cX4 := or(cX4, shl(128, and(c, UINT64_MAX)))

                c := sar(32, mul(sar(192, a), s))
                carry := or(carry, add(c, INT64_SIGN))
                cX4 := or(cX4, shl(192, and(c, UINT64_MAX)))

                mstore(ptrC, cX4) // Store packed `cX4` in `ptrC`.
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

                // Multiply packed `a` with `s` and keep track of carry.
                let c := sar(32, mul(signextend(7, a), s))
                carry := or(carry, add(c, INT64_SIGN))
                let cX4 := and(c, UINT64_MAX)

                c := sar(32, mul(signextend(7, shr(64, a)), s))
                carry := or(carry, add(c, INT64_SIGN))
                cX4 := or(cX4, shl(64, and(c, UINT64_MAX)))

                c := sar(32, mul(signextend(7, shr(128, a)), s))
                carry := or(carry, add(c, INT64_SIGN))
                cX4 := or(cX4, shl(128, and(c, UINT64_MAX)))

                c := sar(32, mul(sar(192, a), s))
                carry := or(carry, add(c, INT64_SIGN))
                cX4 := or(cX4, shl(192, and(c, UINT64_MAX)))

                mstore(ptrC, cX4) // Store packed `cX4` in `ptrC`.
            }
        }

        if (carry > UINT64_MAX) revert __N32x32.N32x32_Overflow();
    }
}

/* ------------- Mat operators ------------- */

function min(M32x32 A) pure returns (N32x32 minValue) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        minValue = MAX; // Set current min to `MAX`.

        // Loop over all `n * m` elements of 8 bytes size.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words (4 elements).
        uint256 end = ptr + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = size & 31;

        // Loop over 32 byte words.
        while (ptr != end) {
            assembly {
                let aX4 := mload(ptr) // Load packed elements at `ptr`.
                let a := signextend(7, aX4)
                if slt(a, minValue) { minValue := a } // Check whether `a < minValue`.

                aX4 := sar(64, aX4)
                a := signextend(7, aX4)
                if slt(a, minValue) { minValue := a } // Check whether `a < minValue`.

                aX4 := sar(64, aX4)
                a := signextend(7, aX4)
                if slt(a, minValue) { minValue := a } // Check whether `a < minValue`.

                a := sar(64, aX4)
                if slt(a, minValue) { minValue := a } // Check whether `a < minValue`.
            }

            ptr = ptr + 32; // Advance pointer to the next slot.
        }

        if (rest != 0) {
            uint256 aX4;

            assembly {
                aX4 := mload(ptr) // Load packed elements at `ptr`.
            }

            // Parse the last remaining word in chunks of 8 bytes.
            while (true) {
                assembly {
                    let a := signextend(7, sar(mul(sub(32, rest), 8), aX4))
                    if slt(a, minValue) { minValue := a } // Check whether `a < minValue`.
                }

                if (rest == 8) break;

                rest = rest - 8;
            }
        }
    }
}

function max(M32x32 A) pure returns (N32x32 maxValue) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        maxValue = MIN; // Set current max to `MIN`.

        // Loop over all `n * m` elements of 8 bytes size.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words (4 elements).
        uint256 end = ptr + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = size & 31;

        // Loop over 32 byte words.
        while (ptr != end) {
            assembly {
                let aX4 := mload(ptr) // Load packed elements at `ptr`.
                let a := signextend(7, aX4)
                if sgt(a, maxValue) { maxValue := a } // Check whether `a > maxValue`.

                aX4 := sar(64, aX4)
                a := signextend(7, aX4)
                if sgt(a, maxValue) { maxValue := a } // Check whether `a > maxValue`.

                aX4 := sar(64, aX4)
                a := signextend(7, aX4)
                if sgt(a, maxValue) { maxValue := a } // Check whether `a > maxValue`.

                a := sar(64, aX4)
                if sgt(a, maxValue) { maxValue := a } // Check whether `a > maxValue`.
            }

            ptr = ptr + 32; // Advance pointer to the next slot.
        }

        if (rest != 0) {
            uint256 aX4;

            assembly {
                aX4 := mload(ptr) // Load packed elements at `ptr`.
            }

            // Parse the last remaining word in chunks of 8 bytes.
            while (true) {
                assembly {
                    // a = (aX4 >> ((32 - rest) * 8)) & UINT64_MAX;
                    let a := signextend(7, sar(mul(sub(32, rest), 8), aX4))
                    if sgt(a, maxValue) { maxValue := a } // Check whether `a > maxValue`.
                }

                if (rest == 8) break;

                rest = rest - 8;
            }
        }
    }
}

function minMax(M32x32 A) pure returns (N32x32 minValue, N32x32 maxValue) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        minValue = MAX; // Set current min to `MAX`.
        maxValue = MIN; // Set current max to `MIN`.

        // Loop over all `n * m` elements of 8 bytes size.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words (4 elements).
        uint256 end = ptr + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = size & 31;

        // Loop over 32 byte words.
        while (ptr != end) {
            assembly {
                let aX4 := mload(ptr) // Load packed elements at `ptr`.
                let a := signextend(7, aX4)
                if slt(a, minValue) { minValue := a } // Check whether `a < minValue`.
                if sgt(a, maxValue) { maxValue := a } // Check whether `a > maxValue`.

                aX4 := sar(64, aX4)
                a := signextend(7, aX4)
                if slt(a, minValue) { minValue := a } // Check whether `a < minValue`.
                if sgt(a, maxValue) { maxValue := a } // Check whether `a > maxValue`.

                aX4 := sar(64, aX4)
                a := signextend(7, aX4)
                if slt(a, minValue) { minValue := a } // Check whether `a < minValue`.
                if sgt(a, maxValue) { maxValue := a } // Check whether `a > maxValue`.

                a := sar(64, aX4)
                if slt(a, minValue) { minValue := a } // Check whether `a < minValue`.
                if sgt(a, maxValue) { maxValue := a } // Check whether `a > maxValue`.
            }

            ptr = ptr + 32; // Advance pointer to the next slot.
        }

        if (rest != 0) {
            uint256 aX4;

            assembly {
                aX4 := mload(ptr) // Load packed elements at `ptr`.
            }

            // Parse the last remaining word in chunks of 8 bytes.
            while (true) {
                assembly {
                    let a := signextend(7, sar(mul(sub(32, rest), 8), aX4))

                    if slt(a, minValue) { minValue := a } // Check whether `a < minValue`.
                    if sgt(a, maxValue) { maxValue := a } // Check whether `a > maxValue`.
                }

                if (rest == 8) break;

                rest = rest - 8;
            }
        }
    }
}

/// @dev Unchecked
function sum(M32x32 A) pure returns (N32x32 s) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        // Loop over all `n * m` elements of 8 bytes.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words (4 elements).
        uint256 end = ptr + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = size & 31;

        // Loop over 32 byte words.
        while (ptr != end) {
            assembly {
                let aX4 := mload(ptr) // Load packed elements at `ptr`.

                // Add each chunk together to `s`.
                s := add(s, signextend(7, aX4))
                s := add(s, signextend(7, sar(64, aX4)))
                s := add(s, signextend(7, sar(128, aX4)))
                s := add(s, sar(192, aX4))
            }

            ptr = ptr + 32; // Advance pointer to the next slot.
        }

        if (rest != 0) {
            uint256 aX4;

            assembly {
                aX4 := mload(ptr) // Load packed elements at `ptr`.
            }

            // Parse the last remaining word in chunks of 8 bytes.
            while (true) {
                assembly {
                    let a := signextend(7, sar(mul(sub(32, rest), 8), aX4))
                    s := add(s, a)
                }

                if (rest == 8) break;

                rest = rest - 8;
            }
        }
    }
}

/// @dev Unchecked
function mean(M32x32 A) pure returns (N32x32 s) {
    unchecked {
        (uint256 n, uint256 m) = shape(A);

        s = A.sum().div(__N32x32.N32x32FromUint(n * m));
    }
}

/// https://en.wikipedia.org/wiki/Algorithms_for_calculating_variance#Computing_shifted_data
/// TODO: introduce shift, overflow protection
/// @dev Unchecked
function vari(M32x32 A) pure returns (N32x32 variance) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        uint256 len = n * m;

        if (len < 2) return ZERO;

        // todo introduce shift
        // uint256 shift;
        // assembly {
        //     shift := mload(ptr)
        // }

        uint256 s;
        uint256 s2;

        // Loop over all `n * m` elements of 8 bytes.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words (4 elements).
        uint256 end = ptr + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = size & 31;

        // Loop over 32 byte words.
        while (ptr != end) {
            assembly {
                let aX4 := mload(ptr) // Load packed elements at `ptr`.

                // Add each chunk together to `s`.
                let a := signextend(7, aX4)
                s := add(s, a)
                s2 := add(s2, shr(32, mul(a, a)))

                aX4 := sar(64, aX4)
                a := signextend(7, aX4)
                s := add(s, a)
                s2 := add(s2, shr(32, mul(a, a)))

                aX4 := sar(64, aX4)
                a := signextend(7, aX4)
                s := add(s, a)
                s2 := add(s2, shr(32, mul(a, a)))

                a := sar(64, aX4)
                s := add(s, a)
                s2 := add(s2, shr(32, mul(a, a)))
            }

            ptr = ptr + 32; // Advance pointer to the next slot.
        }

        if (rest != 0) {
            uint256 aX4;

            assembly {
                aX4 := mload(ptr) // Load packed elements at `ptr`.
            }

            // Parse the last remaining word in chunks of 8 bytes.
            while (rest != 0) {
                assembly {
                    let a := signextend(7, sar(mul(sub(32, rest), 8), aX4))
                    s := add(s, a)
                    s2 := add(s2, shr(32, mul(a, a)))
                }

                rest = rest - 8;
            }
        }

        // note: uses the unbiased version.
        // Use `/ len` for the biased version.
        assembly {
            // variance = (s2 - (s * s >> 32) / len) / (len - 1);
            variance := div(sub(s2, div(shr(32, mul(s, s)), len)), sub(len, 1))
        }
    }
}

function eqAllScalar(M32x32 A, N32x32 s) pure returns (bool equals) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        // Loop over all `n * m` elements of 8 bytes size.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words (4 elements).
        uint256 end = ptr + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = size & 31;
        // Pack `s` in one word for efficiency.
        uint256 sX4 = packWordUnsafe(s, s, s, s);

        equals = true;

        // Loop over 32 byte words.
        while (ptr != end) {
            assembly {
                let aX4 := mload(ptr) // Load packed elements at `ptr`.

                equals := eq(aX4, sX4) // Check whether `a == s`.
            }

            if (!equals) return equals; // Exit early.

            ptr = ptr + 32; // Advance pointer to the next slot.
        }

        if (rest != 0) {
            assembly {
                // Mask applies to leftover bits in word.
                let mask := not(shr(mul(rest, 8), not(0)))
                let aX4 := mload(ptr) // Load packed elements at `ptr`.

                equals := eq(and(mask, aX4), and(mask, sX4))
            }
        }
    }
}

function gtAllScalar(M32x32 A, N32x32 s) pure returns (bool gtResult) {
    unchecked {
        if (s.eq(MAX)) return gtResult = false; // Exit early.

        gtResult = true; // Set initial value to true.

        (uint256 n, uint256 m, uint256 ptr) = header(A);

        // Loop over all `n * m` elements of 8 bytes size.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words (4 elements).
        uint256 end = ptr + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = size & 31;

        // Loop over 32 byte words.
        while (ptr != end) {
            assembly {
                let aX4 := mload(ptr) // Load packed elements at `ptr`.

                gtResult := sgt(signextend(7, aX4), s) // Check whether `a > s`.
                aX4 := sar(64, aX4)
                gtResult := and(gtResult, sgt(signextend(7, aX4), s)) // Check whether `a > s`.
                aX4 := sar(64, aX4)
                gtResult := and(gtResult, sgt(signextend(7, aX4), s)) // Check whether `a > s`.
                aX4 := sar(64, aX4)
                gtResult := and(gtResult, sgt(aX4, s)) // Check whether `a > s`.
            }

            if (!gtResult) return gtResult; // Exit early.

            ptr = ptr + 32; // Advance pointer to the next slot.
        }

        if (rest != 0) {
            uint256 aX4;

            assembly {
                aX4 := mload(ptr) // Load packed elements at `ptr`.
            }

            // Parse the last remaining word in chunks of 8 bytes.
            while (true) {
                assembly {
                    let a := signextend(7, sar(mul(sub(32, rest), 8), aX4))
                    gtResult := and(gtResult, sgt(a, s)) // Check whether `a > s`.
                }

                if (rest == 8) break;

                rest = rest - 8;
            }
        }
    }
}

function gteAllScalar(M32x32 A, N32x32 s) pure returns (bool gteResult) {
    unchecked {
        if (s.eq(MIN)) return true; // Exit early.

        gteResult = gtAllScalar(A, s.sub(N32x32.wrap(1))); // Reduce `s` so we can use `gt`.
    }
}

function ltAllScalar(M32x32 A, N32x32 s) pure returns (bool ltResult) {
    unchecked {
        if (s.eq(MIN)) return ltResult = false; // Exit early.

        ltResult = true; // Set initial value to true.

        (uint256 n, uint256 m, uint256 ptr) = header(A);

        // Loop over all `n * m` elements of 8 bytes size.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words (4 elements).
        uint256 end = ptr + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = size & 31;

        // Loop over 32 byte words.
        while (ptr != end) {
            assembly {
                let aX4 := mload(ptr) // Load packed elements at `ptr`.

                ltResult := slt(signextend(7, aX4), s) // Check whether `a < s`.
                aX4 := sar(64, aX4)
                ltResult := and(ltResult, slt(signextend(7, aX4), s)) // Check whether `a < s`.
                aX4 := sar(64, aX4)
                ltResult := and(ltResult, slt(signextend(7, aX4), s)) // Check whether `a < s`.
                aX4 := sar(64, aX4)
                ltResult := and(ltResult, slt(aX4, s)) // Check whether `a < s`.
            }

            if (!ltResult) return ltResult; // Exit early.

            ptr = ptr + 32; // Advance pointer to the next slot.
        }

        if (rest != 0) {
            uint256 aX4;

            assembly {
                aX4 := mload(ptr) // Load packed elements at `ptr`.
            }

            // Parse the last remaining word in chunks of 8 bytes.
            while (true) {
                assembly {
                    let a := signextend(7, sar(mul(sub(32, rest), 8), aX4))
                    ltResult := and(ltResult, slt(a, s)) // Check whether `a < s`.
                }

                if (rest == 8) break;

                rest = rest - 8;
            }
        }
    }
}

function lteAllScalar(M32x32 A, N32x32 s) pure returns (bool lteResult) {
    unchecked {
        if (s.eq(MAX)) return lteResult = true; // Exit early.

        lteResult = ltAllScalar(A, s.add(N32x32.wrap(1))); // Increase by `1` and use `ltAllScalar`.
    }
}

function full(uint256 n, uint256 m, N32x32 s) pure returns (M32x32 C) {
    C = mallocM32x32(n, m); // Allocate memory for matrix.

    fill_(C, s); // Fill matrix with `s`.
}

function fill_(M32x32 A, N32x32 s) pure {
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

/// @dev TODO optimize
function neg(M32x32 A) pure returns (M32x32 C) {
    C = mulScalar(A, NEG_ONE);
}

function abs(M32x32 A) pure returns (M32x32 C) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrA) = header(A);

        C = mallocM32x32(n, m); // Allocate memory for matrix.

        // Loop over all `n * m` elements of 8 bytes.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words (4 elements).
        uint256 endA = ptrA + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = size & 31;
        // Obtain a pointer to `C`s data location.
        uint256 ptrC = ref(C);
        // Keep track of overflow.
        bool overflow;

        // Loop over 32 byte words.
        while (ptrA != endA) {
            assembly {
                let cX4 := mload(ptrA) // Load 4 values from `A` at `ptrA`.

                if and(cX4, INT64_SIGN) {
                    let negated := and(add(not(cX4), 1), UINT64_MAX)
                    overflow := or(overflow, eq(negated, INT64_SIGN))
                    cX4 := or(and(cX4, not(UINT64_MAX)), negated)
                }

                if and(cX4, shl(64, INT64_SIGN)) {
                    let negated := and(add(not(shr(64, cX4)), 1), UINT64_MAX)
                    overflow := or(overflow, eq(negated, INT64_SIGN))
                    cX4 := or(and(cX4, not(shl(64, UINT64_MAX))), shl(64, negated))
                }

                if and(cX4, shl(128, INT64_SIGN)) {
                    let negated := and(add(not(shr(128, cX4)), 1), UINT64_MAX)
                    overflow := or(overflow, eq(negated, INT64_SIGN))
                    cX4 := or(and(cX4, not(shl(128, UINT64_MAX))), shl(128, negated))
                }

                if and(cX4, shl(192, INT64_SIGN)) {
                    let negated := and(add(not(shr(192, cX4)), 1), UINT64_MAX)
                    overflow := or(overflow, eq(negated, INT64_SIGN))
                    cX4 := or(and(cX4, not(shl(192, UINT64_MAX))), shl(192, negated))
                }

                mstore(ptrC, cX4) // Store packed `cX4` in `ptrC`.
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
                // Load 4 values from `A` at `ptrA`.
                let cX4 := and(mload(ptrA), mask)

                if and(cX4, shl(64, INT64_SIGN)) {
                    let negated := and(add(not(shr(64, cX4)), 1), UINT64_MAX)
                    overflow := or(overflow, eq(negated, INT64_SIGN))
                    cX4 := or(and(cX4, not(shl(64, UINT64_MAX))), shl(64, negated))
                }

                if and(cX4, shl(128, INT64_SIGN)) {
                    let negated := and(add(not(shr(128, cX4)), 1), UINT64_MAX)
                    overflow := or(overflow, eq(negated, INT64_SIGN))
                    cX4 := or(and(cX4, not(shl(128, UINT64_MAX))), shl(128, negated))
                }

                if and(cX4, shl(192, INT64_SIGN)) {
                    let negated := and(add(not(shr(192, cX4)), 1), UINT64_MAX)
                    overflow := or(overflow, eq(negated, INT64_SIGN))
                    cX4 := or(and(cX4, not(shl(192, UINT64_MAX))), shl(192, negated))
                }

                mstore(ptrC, cX4) // Store packed `cX4` in `ptrC`.
            }
        }

        if (overflow) revert __N32x32.N32x32_Overflow();
    }
}

function T(M32x32 A) pure returns (M32x32 C) {
    C = transpose(A);
}

function transposeNaive(M32x32 A) pure returns (M32x32 C) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrAj) = header(A);

        if (n == 1 || m == 1) return C = A.reshape(m, n);

        C = mallocM32x32(m, n); // Allocate memory for matrix.

        uint256 ptrCi = ref(C) - 24;
        ptrAj = ptrAj - 24;

        uint256 rowSizeA = 8 * m;
        uint256 rowSizeC = 8 * n;
        // End iterating over `A`s columns when arriving at the last column.
        uint256 ptrAjEnd = ptrAj + rowSizeA;

        // Loop over `A`s rows →.
        while (ptrAj != ptrAjEnd) {
            uint256 ptrA = ptrAj; // Start at the beginning of the current column.
            uint256 ptrC = ptrCi; // Start at the beginning of the current row.
            uint256 ptrCEnd = ptrCi + rowSizeC; // End at the last element of the current row.

            // Loop over `C`s columns ↓.
            while (ptrC != ptrCEnd) {
                assembly {
                    let preserveWord := and(mload(ptrC), not(UINT64_MAX))
                    let a := and(mload(ptrA), UINT64_MAX)
                    let c := or(preserveWord, a)

                    mstore(ptrC, c) // Copy element from `A` to `C`.
                }

                ptrC = ptrC + 8; // Advance to the next column →.
                ptrA = ptrA + rowSizeA; // Advance to the next row ↓.
            }

            ptrAj = ptrAj + 8; // Advance to the next column → of `A`.
            ptrCi = ptrCi + rowSizeC; // Advance to the next row ↓ of `C`.
        }
    }
}

function transpose(M32x32 A) pure returns (M32x32 C) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrACol) = header(A);

        if (n == 1 || m == 1) return C = A.reshape(m, n);

        C = mallocM32x32(m, n); // Allocate memory for matrix.

        uint256 ptrCRow = ref(C);

        uint256 rowSizeA = 8 * m;
        uint256 colSizeA = 8 * n;
        uint256 ptrAColEnd;

        if (colSizeA & 31 != 0) {
            // Handle partial blocks of `A` containing less than 4 rows.
            // Note: This step adds dirty values to `C` when not preserving the existing memory.
            //       However, as this is done before the main block loop,
            //       any dirty values will be overwritten later.
            // ┌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┬╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┐
            // ╎  1     2     3     4   ╎  5     6     7   ┆
            // ╎  8     9     10    11  ╎  12    13    14  ┆
            // ╎  15    16    17    18  ╎  19    20    21  ┆
            // ╎  22    23    24    25  ╎  26    27    28  ┆
            // ┢━━━━━━━━━━━━━━━━━━━━━━━━╅╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┤
            // ┃  29    30    31    32  ┃  33    34    35  ┆
            // ┃  36    37    38    39  ┃  40    41    42  ┆
            // ┃  43    44    45    46  ┃  47    48    49  ┆
            // ┗━━━━━━━━━━━━━━━━━━━━━━━━┹╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┘
            //
            // Place `ptrA` at the beginning of the first row of `A` that is not a multiple of 4.
            ptrACol = ref(A) + (colSizeA & ~uint256(31)) * m;
            // Place `ptrC` at the corresponding location in `C`.
            ptrCRow = ref(C) + (colSizeA & ~uint256(31));
            // End at last full multiple of 4.
            ptrAColEnd = ptrACol + (rowSizeA & ~uint256(31));

            // Loop over `A`s columns → (`C`s rows ↓) in strides of 4.
            while (ptrACol != ptrAColEnd) {
                // NOTE: move out.
                uint256 ptrA = ptrACol; // Start at the beginning of the current column.
                uint256 ptrC = ptrCRow; // Start at the beginning of the current row.

                assembly {
                    // Load block of packed elements of the next 3 rows and 4 columns of `A`: `A[i:i+3,j:j+4]`.
                    // The last row is not used required, as otherwise the row count would have been divisible by 4.
                    // We might not require all 4 columns, however these will be overwritten later in the main loop.
                    let a1X4 := mload(ptrA) // Load packed A[i+0,j:j+4].
                    ptrA := add(ptrA, rowSizeA) // Advance to the next row ↓ of `A`.
                    let a2X4 := mload(ptrA) // Load packed A[i+1,j:j+4].
                    ptrA := add(ptrA, rowSizeA) // Advance to the next row ↓ of `A`.
                    let a3X4 := mload(ptrA) // Load packed A[i+2,j:j+4].

                    // Pack elements from `A[i:i+3,j]` into `C[j,i:i+3]`.
                    let mask := shl(192, UINT64_MAX)
                    let c1X4 := and(a1X4, mask)
                    c1X4 := or(c1X4, shr(64, and(a2X4, mask)))
                    c1X4 := or(c1X4, shr(128, and(a3X4, mask)))

                    mstore(ptrC, c1X4) // Copy packed elements from `A` to `C`.

                    // Pack elements from `A[i:i+3,j+1]` into `C[j+1,i:i+3]`.
                    mask := shl(128, UINT64_MAX)
                    let c2X4 := shl(64, and(a1X4, mask))
                    c2X4 := or(c2X4, and(a2X4, mask))
                    c2X4 := or(c2X4, shr(64, and(a3X4, mask)))

                    mstore(add(ptrC, colSizeA), c2X4) // Copy packed elements from `A` to `C`.

                    // Pack elements from `A[i:i+3,j+2]` into `C[j+2,i:i+3]`.
                    mask := shl(64, UINT64_MAX)
                    let c3X4 := shl(128, and(a1X4, mask))
                    c3X4 := or(c3X4, shl(64, and(a2X4, mask)))
                    c3X4 := or(c3X4, and(a3X4, mask))

                    mstore(add(ptrC, mul(colSizeA, 2)), c3X4) // Copy packed elements from `A` to `C`.

                    // Pack elements from `A[i:i+3,j+3]` into `C[j+3,i:i+3]`.
                    let c4X4 := shl(192, and(a1X4, UINT64_MAX))
                    c4X4 := or(c4X4, shl(128, and(a2X4, UINT64_MAX)))
                    c4X4 := or(c4X4, shl(64, and(a3X4, UINT64_MAX)))

                    mstore(add(ptrC, mul(colSizeA, 3)), c4X4) // Copy packed elements from `A` to `C`.
                }

                ptrACol = ptrACol + 32; // Advance column pointer to the next column → of `A` in strides of 4.
                ptrCRow = ptrCRow + 4 * colSizeA; // Advance row pointer to the next row ↓ of `C` in strides of 4.
            }
        }

        // Handle all blocks of 4x4 elements.
        //
        // ┏━━━━━━━━━━━━━━━━━━━━━━━━┱╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┐
        // ┃  1     2     3     4   ┃  5     6     7   ┆
        // ┃  8     9     10    11  ┃  12    13    14  ┆
        // ┃  15    16    17    18  ┃  19    20    21  ┆
        // ┃  22    23    24    25  ┃  26    27    28  ┆
        // ┡━━━━━━━━━━━━━━━━━━━━━━━━╃╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┤
        // ╎  29    30    31    32  ╎  33    34    35  ┆
        // ╎  36    37    38    39  ╎  40    41    42  ┆
        // ╎  43    44    45    46  ╎  47    48    49  ┆
        // └╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┴╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┘
        ptrACol = ref(A);
        ptrCRow = ref(C);
        // End iterating over `A`s columns ➞ when arriving at the last column multiple of 4.
        ptrAColEnd = ptrACol + (rowSizeA & ~uint256(31));

        // Outer loop over `A`s columns → (`C`s rows ↓) in strides of 4.
        while (ptrACol != ptrAColEnd) {
            uint256 ptrA = ptrACol; // Start at the beginning of the current column.
            uint256 ptrC = ptrCRow; // Start at the beginning of the current row.
            uint256 ptrCEnd = ptrCRow + (colSizeA & ~uint256(31)); // End at the last element of the current row.

            // Inner loop over `A`s rows ↓ (`C`s columns →) in strides of 4.
            while (ptrC != ptrCEnd) {
                assembly {
                    // Load block of packed elements of the next 4 rows and columns of `A`: `A[i:i+4,j:j+4]`.
                    let a1X4 := mload(ptrA) // Load packed A[i+0,j:j+4].
                    ptrA := add(ptrA, rowSizeA) // Advance to the next row ↓ of `A`.
                    let a2X4 := mload(ptrA) // Load packed A[i+1,j:j+4].
                    ptrA := add(ptrA, rowSizeA) // Advance to the next row ↓ of `A`.
                    let a3X4 := mload(ptrA) // Load packed A[i+2,j:j+4].
                    ptrA := add(ptrA, rowSizeA) // Advance to the next row ↓ of `A`.
                    let a4X4 := mload(ptrA) // Load packed A[i+3,j:j+4].
                    ptrA := add(ptrA, rowSizeA) // Advance to the next row ↓ of `A`.

                    // Pack elements from `A[i:i+4,j]` into `C[j,i:i+4]`.
                    let mask := shl(192, UINT64_MAX)
                    let c1X4 := and(a1X4, mask)
                    c1X4 := or(c1X4, shr(64, and(a2X4, mask)))
                    c1X4 := or(c1X4, shr(128, and(a3X4, mask)))
                    c1X4 := or(c1X4, shr(192, and(a4X4, mask)))

                    mstore(ptrC, c1X4) // Copy packed elements from `A` to `C`.

                    // Pack elements from `A[i:i+4,j+1]` into `C[j+1,i:i+4]`.
                    mask := shl(128, UINT64_MAX)
                    let c2X4 := shl(64, and(a1X4, mask))
                    c2X4 := or(c2X4, and(a2X4, mask))
                    c2X4 := or(c2X4, shr(64, and(a3X4, mask)))
                    c2X4 := or(c2X4, shr(128, and(a4X4, mask)))

                    mstore(add(ptrC, colSizeA), c2X4) // Copy packed elements from `A` to `C`.

                    // Pack elements from `A[i:i+4,j+2]` into `C[j+2,i:i+4]`.
                    mask := shl(64, UINT64_MAX)
                    let c3X4 := shl(128, and(a1X4, mask))
                    c3X4 := or(c3X4, shl(64, and(a2X4, mask)))
                    c3X4 := or(c3X4, shr(0, and(a3X4, mask)))
                    c3X4 := or(c3X4, shr(64, and(a4X4, mask)))

                    mstore(add(ptrC, mul(colSizeA, 2)), c3X4) // Copy packed elements from `A` to `C`.

                    // Pack elements from `A[i:i+4,j+3]` into `C[j+3,i:i+4]`.
                    let c4X4 := shl(192, and(a1X4, UINT64_MAX))
                    c4X4 := or(c4X4, shl(128, and(a2X4, UINT64_MAX)))
                    c4X4 := or(c4X4, shl(64, and(a3X4, UINT64_MAX)))
                    c4X4 := or(c4X4, and(a4X4, UINT64_MAX))

                    mstore(add(ptrC, mul(colSizeA, 3)), c4X4) // Copy packed elements from `A` to `C`.
                }

                ptrC = ptrC + 32; // Advance to the next column → in strides of 4.
            }

            ptrACol = ptrACol + 32; // Advance column pointer to the next column → of `A` in strides of 4.
            // FIX
            ptrCRow = ptrCRow + 4 * colSizeA; // Advance row pointer to the next row ↓ of `C` in strides of 4.
        }

        if (rowSizeA & 31 != 0) {
            uint256 ptrARow;
            uint256 ptrARowEnd;
            uint256 ptrCCol;

            // Handle the last rows of `A` that are not a multiple of 4.
            // ┌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┲━━━━━━━━━━━━━━━━━━┓
            // ┆  1     2     3     4   ┃  5     6     7   ┃
            // ┆  8     9     10    11  ┃  12    13    14  ┃
            // ┆  15    16    17    18  ┃  19    20    21  ┃
            // ┆  22    23    24    25  ┃  26    27    28  ┃
            // ├╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╊━━━━━━━━━━━━━━━━━━┫
            // ╎  29    30    31    32  ┃  33    34    35  ┃
            // ╎  36    37    38    39  ┃  40    41    42  ┃
            // ╎  43    44    45    46  ┃  47    48    49  ┃
            // └╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌┺━━━━━━━━━━━━━━━━━━┛
            //
            // Place `ptrA` at the beginning of the first column of `A` that is not a multiple of 4.
            ptrARow = ref(A) + (rowSizeA & ~uint256(31));
            // Place `ptrC` at the corresponding location in `C`.
            ptrCCol = ref(C) + (rowSizeA & ~uint256(31)) * n;
            // End at last full multiple of 4.
            ptrARowEnd = ptrARow + (colSizeA & ~uint256(31)) * m;

            // Reverse order, so that we don't need to mask words.
            (ptrARow, ptrARowEnd) = (ptrARowEnd, ptrARow);
            ptrCCol = ptrCCol + (colSizeA & ~uint256(31));

            // Loop over `A`s rows ↓ (`C`s columns →) in strides of 4 (in reverse order).
            while (true) {
                // NOTE: move out.
                uint256 ptrA = ptrARow; // Start at the beginning of the current column.
                uint256 ptrC = ptrCCol; // Start at the beginning of the current row.

                uint256 a1X4;
                uint256 a2X4;
                uint256 a3X4;
                uint256 a4X4;

                assembly {
                    // Load block of packed elements of the next 3 rows and 4 columns of `A`: `A[i:i+3,j:j+4]`.
                    a1X4 := mload(ptrA) // Load packed A[i+0,j:j+4].
                    ptrA := add(ptrA, rowSizeA) // Advance to the next row ↓ of `A`.
                    a2X4 := mload(ptrA) // Load packed A[i+1,j:j+4].
                    ptrA := add(ptrA, rowSizeA) // Advance to the next row ↓ of `A`.
                    a3X4 := mload(ptrA) // Load packed A[i+2,j:j+4].
                    ptrA := add(ptrA, rowSizeA) // Advance to the next row ↓ of `A`.
                    a4X4 := mload(ptrA) // Load packed A[i+2,j:j+4].

                    // Pack elements from `A[i:i+3,j]` into `C[j,i:i+3]`.
                    let mask := shl(192, UINT64_MAX)
                    let c1X4 := and(a1X4, mask)
                    c1X4 := or(c1X4, shr(64, and(a2X4, mask)))
                    c1X4 := or(c1X4, shr(128, and(a3X4, mask)))
                    c1X4 := or(c1X4, shr(192, a4X4))

                    mstore(ptrC, c1X4) // Copy packed elements from `A` to `C`.
                }

                if (rowSizeA & 31 > 15) {
                    assembly {
                        // Pack elements from `A[i:i+3,j+1]` into `C[j+1,i:i+3]`.
                        let mask := shl(128, UINT64_MAX)
                        let c2X4 := shl(64, and(a1X4, mask))
                        c2X4 := or(c2X4, and(a2X4, mask))
                        c2X4 := or(c2X4, shr(64, and(a3X4, mask)))
                        c2X4 := or(c2X4, shr(128, and(a4X4, mask)))

                        mstore(add(ptrC, colSizeA), c2X4) // Copy packed elements from `A` to `C`.
                    }

                    if (rowSizeA & 31 == 24) {
                        assembly {
                            // Pack elements from `A[i:i+3,j+2]` into `C[j+2,i:i+3]`.
                            let mask := shl(64, UINT64_MAX)
                            let c3X4 := shl(128, and(a1X4, mask))
                            c3X4 := or(c3X4, shl(64, and(a2X4, mask)))
                            c3X4 := or(c3X4, and(a3X4, mask))
                            c3X4 := or(c3X4, shr(64, and(a4X4, mask)))

                            mstore(add(ptrC, mul(colSizeA, 2)), c3X4) // Copy packed elements from `A` to `C`.
                        }
                    }
                }

                if (ptrARow == ptrARowEnd) break;

                // Note: Traversing in reverse order to avoid masking.
                ptrARow = ptrARow - 4 * rowSizeA; // Advance row pointer to the next row ↓ of `A` in strides of 4.
                ptrCCol = ptrCCol - 32; // Advance column pointer to the next column → of `C` in strides of 4.
            }
        }
    }
}

function map(M32x32 A, function (uint256) returns (uint256) fn) returns (M32x32 C) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrA) = header(A);

        C = mallocM32x32(m, n); // Allocate memory for matrix.

        uint256 ptrC = ref(C); // Obtain a pointer to `C`s data location.

        // Loop over all `n * m` elements of 8 bytes size.
        uint256 end = ptrA + n * m * 8;

        while (ptrA != end) {
            uint256 a;

            assembly {
                a := mload(ptrA) // Load element at `ptrA`.
            }

            uint256 c = fn(a);

            assembly {
                mstore(ptrC, c) // Store `c` at `ptrC`.
            }

            ptrA = ptrA + 8; // Advance pointer to the next slot.
            ptrC = ptrC + 8; // Advance pointer to the next slot.
        }
    }
}

/* ------------- conversions ------------- */

function copy(M32x32 A) view returns (M32x32 C) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrA) = header(A);

        C = mallocM32x32(n, m); // Allocate memory for matrix.

        __UM256.mcopy(ptrA, ref(C), n * m * 8); // Copy data from `ptrA` to `ptrC`.
    }
}

// function fromEncodedPacked_(bytes memory dataBytes) pure returns (M32x32 C) {
//     C = fromEncodedPacked_(dataBytes, 1, dataBytes.length / 8);
// }

// function fromEncoded(bytes memory dataBytes, uint256 n, uint256 m) pure returns (M32x32 C) {
//     unchecked {
//         if (n * m * 32 > dataBytes.length) revert M32x32_TooLarge();

//         uint256 dataPtr;

//         assembly {
//             dataPtr := add(32, dataBytes) // Actual data is located after length encoding.
//         }

//         C = mallocM32x32(n, m);
//         // C = M32x32Header(dataPtr, n, m); // Generate header without allocating memory.
//     }
// }

// function bytes_(M32x32 A) pure returns (bytes memory dataBytes) {
//     uint256 ptr = ref(A);

//     assembly {
//         // This only works under the assumption that
//         // we always store the size in bytes before the data.
//         dataBytes := sub(ptr, 32)
//     }
// }
// fromUint256Ptr

function fromUintArray(uint256[][] memory data) pure returns (M32x32 C) {
    unchecked {
        uint256 n = data.length;

        if (n == 0) return C = mallocM32x32(0, 0);

        uint256 m = data[0].length;

        uint256 rowPtr;
        assembly {
            rowPtr := add(data, 0x20)
        }

        C = mallocM32x32(n, m); // Allocate new matrix of the same dimensions.

        uint256 ptrC = ref(C); // Obtain a reference to `C`s data.

        uint256 carry; // Keep track of overflow.
        uint256 rowSize = m * 32;
        uint256 rowPtrEnd = rowPtr + n * 32; // Stop after parsing `n` rows.

        while (rowPtr != rowPtrEnd) {
            uint256 ptr;
            uint256 rowLen;

            assembly {
                ptr := mload(rowPtr) // Load row data location.
                rowLen := mload(ptr) // Load length of row data.
                ptr := add(ptr, 0x20) // Data starts after 32 bytes.
            }

            if (rowLen != m) revert M32x32_InvalidDimensions();

            uint256 end = ptr + (rowSize & ~uint256(127)); // Up until here we can load & parse full words (4 elements).
            uint256 rest = rowSize & 127; // The rest needs to be parsed individually.

            while (ptr != end) {
                assembly {
                    let a1, a2, a3, a4, cX4

                    // Load 4 values from `A` at `ptr`.
                    a1 := mload(ptr)
                    a2 := mload(add(0x20, ptr))
                    a3 := mload(add(0x40, ptr))
                    a4 := mload(add(0x60, ptr))

                    // Pack values into `cX4`.
                    cX4 := shl(224, a1)
                    cX4 := or(cX4, shl(160, a2))
                    cX4 := or(cX4, shl(96, a3))
                    cX4 := or(cX4, shl(32, a4))

                    mstore(ptrC, cX4) // Store packed values in `ptrC`.

                    // Keep track of overflow.
                    carry := or(carry, a1)
                    carry := or(carry, a2)
                    carry := or(carry, a3)
                    carry := or(carry, a4)
                }

                // Advance pointers to the next slots.
                ptr = ptr + 0x80;
                ptrC = ptrC + 0x20;
            }

            // Parse the last remaining chunk.
            if (rest != 0) {
                assembly {
                    // Mask applies to leftover bits in word.
                    let mask := not(shr(mul(rest, 2), not(0)))
                    let a1, a2, a3, cX4

                    // Load 3 values from `A` at `ptr`.
                    a1 := mload(ptr)
                    a2 := mload(add(0x20, ptr))
                    a3 := mload(add(0x40, ptr))

                    // Pack values into `cX4`.
                    cX4 := shl(224, a1)
                    cX4 := or(cX4, shl(160, and(a2, UINT32_MAX)))
                    cX4 := or(cX4, shl(96, and(a3, UINT32_MAX)))

                    mstore(ptrC, and(cX4, mask)) // Store packed `c` in `ptrC`.

                    // Keep track of overflow.
                    carry := or(carry, a1)
                    carry := or(carry, mul(a2, gt(rest, 0x20)))
                    carry := or(carry, mul(a3, gt(rest, 0x40)))

                    ptrC := add(ptrC, shr(2, rest))
                }
            }

            rowPtr = rowPtr + 0x20;
        }

        if (carry > uint256(INT32_MAX)) revert __N32x32.N32x32_Overflow();
    }
}

function fromUintEncoded(bytes memory dataBytes) pure returns (M32x32 C) {
    unchecked {
        uint256 m = dataBytes.length / 32;

        uint256 ptr;

        assembly {
            ptr := add(32, dataBytes) // Actual data is located after length encoding.
        }

        C = mallocM32x32(1, m);

        fromUintPtrTo_(ptr, C); // Copy words from `ptr` to packed `C`.
    }
}

function fromUintPtrTo_(uint256 ptr, M32x32 C) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrC) = header(C);
        // Loop over all `n * m` elements of 32 bytes.
        uint256 size = n * m * 32;
        // Up until here we can load & parse full words (4 elements).
        uint256 end = ptr + (size & ~uint256(127));
        // The rest needs to be parsed individually.
        uint256 rest = size & 127;
        // Keep track of overflow.
        uint256 carry;

        while (ptr != end) {
            assembly {
                let a1, a2, a3, a4, cX4

                // Load 4 values from `A` at `ptr`.
                a1 := mload(ptr)
                a2 := mload(add(0x20, ptr))
                a3 := mload(add(0x40, ptr))
                a4 := mload(add(0x60, ptr))

                // Pack values into `cX4`.
                cX4 := shl(224, a1)
                cX4 := or(cX4, shl(160, a2))
                cX4 := or(cX4, shl(96, a3))
                cX4 := or(cX4, shl(32, a4))

                mstore(ptrC, cX4) // Store packed values in `ptrC`.

                // Keep track of overflow.
                carry := or(carry, a1)
                carry := or(carry, a2)
                carry := or(carry, a3)
                carry := or(carry, a4)
            }

            // Advance pointers to the next slot.
            ptr = ptr + 0x80;
            ptrC = ptrC + 0x20;
        }

        // Parse the last remaining chunk.
        if (rest != 0) {
            assembly {
                // Mask applies to leftover bits in word.
                let mask := not(shr(mul(rest, 2), not(0)))
                let a1, a2, a3, cX4

                // Load 3 values from `A` at `ptr`.
                a1 := mload(ptr)
                a2 := mload(add(0x20, ptr))
                a3 := mload(add(0x40, ptr))

                // Pack values into `cX4`.
                cX4 := shl(224, a1)
                cX4 := or(cX4, shl(160, and(a2, UINT64_MAX)))
                cX4 := or(cX4, shl(96, and(a3, UINT64_MAX)))

                mstore(ptrC, and(cX4, mask)) // Store packed `c` in `ptrC`.

                // Keep track of overflow.
                carry := or(carry, a1)
                carry := or(carry, mul(a2, gt(rest, 0x20)))
                carry := or(carry, mul(a3, gt(rest, 0x40)))
            }
        }

        if (carry > uint256(INT32_MAX)) revert __N32x32.N32x32_Overflow();
    }
}

function fromIntEncoded(bytes memory dataBytes) pure returns (M32x32 C) {
    unchecked {
        uint256 m = dataBytes.length / 32;

        uint256 ptr;

        assembly {
            ptr := add(32, dataBytes) // Actual data is located after length encoding.
        }

        C = mallocM32x32(1, m);

        fromIntPtrTo_(ptr, C); // Copy words from `ptr` to packed `C`.
    }
}

function fromIntPtrTo_(uint256 ptr, M32x32 C) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrC) = header(C);
        // Loop over all `n * m` elements of 32 bytes.
        uint256 size = n * m * 32;
        // Up until here we can load & parse full words (4 elements).
        uint256 end = ptr + (size & ~uint256(127));
        // The rest needs to be parsed individually.
        uint256 rest = size & 127;
        // Keep track of overflow.
        uint256 carry;

        while (ptr != end) {
            assembly {
                let a1, a2, a3, a4, cX4

                // Load 4 values from `A` at `ptr`.
                a1 := mload(ptr)
                a2 := mload(add(0x20, ptr))
                a3 := mload(add(0x40, ptr))
                a4 := mload(add(0x60, ptr))

                // Pack values into `cX4`.
                cX4 := shl(224, a1)
                cX4 := or(cX4, shl(160, and(a2, UINT32_MAX)))
                cX4 := or(cX4, shl(96, and(a3, UINT32_MAX)))
                cX4 := or(cX4, shl(32, and(a4, UINT32_MAX)))

                mstore(ptrC, cX4) // Store packed values in `ptrC`.

                // Keep track of overflow.
                carry := or(carry, add(a1, INT32_SIGN))
                carry := or(carry, add(a2, INT32_SIGN))
                carry := or(carry, add(a3, INT32_SIGN))
                carry := or(carry, add(a4, INT32_SIGN))
            }

            // Advance pointers to the next slot.
            ptr = ptr + 0x80;
            ptrC = ptrC + 0x20;
        }

        // Parse the last remaining chunk.
        if (rest != 0) {
            assembly {
                // Mask applies to leftover bits in word.
                let mask := not(shr(mul(rest, 2), not(0)))
                let a1, a2, a3, cX4

                // Load 3 values from `A` at `ptr`.
                a1 := mload(ptr)
                a2 := mload(add(0x20, ptr))
                a3 := mload(add(0x40, ptr))

                // Pack values into `cX4`.
                cX4 := shl(224, a1)
                cX4 := or(cX4, shl(160, and(a2, UINT32_MAX)))
                cX4 := or(cX4, shl(96, and(a3, UINT32_MAX)))

                mstore(ptrC, and(cX4, mask)) // Store packed `c` in `ptrC`.

                // Keep track of overflow.
                carry := or(carry, add(a1, INT32_SIGN))
                carry := or(carry, mul(add(a2, INT32_SIGN), gt(rest, 0x20)))
                carry := or(carry, mul(add(a3, INT32_SIGN), gt(rest, 0x40)))
            }
        }

        if (carry > UINT32_MAX) revert __N32x32.N32x32_Overflow();
    }
}

function fromIntArray(int256[][] memory data) pure returns (M32x32 C) {
    unchecked {
        uint256 n = data.length;

        if (n == 0) return C = mallocM32x32(0, 0);

        uint256 m = data[0].length;

        uint256 rowPtr;
        assembly {
            rowPtr := add(data, 0x20)
        }

        C = mallocM32x32(n, m); // Allocate new matrix of the same dimensions.

        uint256 ptrC = ref(C); // Obtain a reference to `C`s data.

        uint256 carry; // Keep track of overflow.
        uint256 rowSize = m * 32; // Compute size of row.
        uint256 rowPtrEnd = rowPtr + n * 32; // Stop after parsing `n` rows.

        while (rowPtr != rowPtrEnd) {
            uint256 ptr;
            uint256 rowLen;

            assembly {
                ptr := mload(rowPtr) // Load row data location.
                rowLen := mload(ptr) // Load length of row data.
                ptr := add(ptr, 0x20) // Data starts after 32 bytes.
            }

            if (rowLen != m) revert M32x32_InvalidDimensions();

            uint256 end = ptr + (rowSize & ~uint256(127)); // Up until here we can load & parse full words (4 elements).
            uint256 rest = rowSize & 127; // The rest needs to be parsed individually.

            while (ptr != end) {
                assembly {
                    let a1, a2, a3, a4, cX4

                    // Load 4 values from `A` at `ptr`.
                    a1 := mload(ptr)
                    a2 := mload(add(0x20, ptr))
                    a3 := mload(add(0x40, ptr))
                    a4 := mload(add(0x60, ptr))

                    // Pack values into `cX4`.
                    cX4 := shl(224, a1)
                    cX4 := or(cX4, shl(160, and(a2, UINT32_MAX)))
                    cX4 := or(cX4, shl(96, and(a3, UINT32_MAX)))
                    cX4 := or(cX4, shl(32, and(a4, UINT32_MAX)))

                    mstore(ptrC, cX4) // Store packed values in `ptrC`.

                    // Keep track of overflow.
                    carry := or(carry, add(a1, INT32_SIGN))
                    carry := or(carry, add(a2, INT32_SIGN))
                    carry := or(carry, add(a3, INT32_SIGN))
                    carry := or(carry, add(a4, INT32_SIGN))
                }

                // Advance pointers to the next slots.
                ptr = ptr + 0x80;
                ptrC = ptrC + 0x20;
            }

            // Parse the last remaining chunk.
            if (rest != 0) {
                assembly {
                    // Mask applies to leftover bits in word.
                    let mask := not(shr(mul(rest, 2), not(0)))
                    let a1, a2, a3, cX4

                    // Load 3 values from `A` at `ptr`.
                    a1 := mload(ptr)
                    a2 := mload(add(0x20, ptr))
                    a3 := mload(add(0x40, ptr))

                    // Pack values into `cX4`.
                    cX4 := shl(224, a1)
                    cX4 := or(cX4, shl(160, and(a2, UINT32_MAX)))
                    cX4 := or(cX4, shl(96, and(a3, UINT32_MAX)))

                    mstore(ptrC, and(cX4, mask)) // Store packed `c` in `ptrC`.

                    // Keep track of overflow.
                    carry := or(carry, add(a1, INT32_SIGN))
                    carry := or(carry, mul(add(a2, INT32_SIGN), gt(rest, 0x20)))
                    carry := or(carry, mul(add(a3, INT32_SIGN), gt(rest, 0x40)))

                    ptrC := add(ptrC, shr(2, rest))
                }
            }

            rowPtr = rowPtr + 0x20;
        }

        if (carry > UINT32_MAX) revert __N32x32.N32x32_Overflow();
    }
}

/* ------------- unsafe conversions ------------- */

function fromUintArray(uint8[3][3] memory data) pure returns (M32x32 C) {
    C = mallocM32x32(3, 3); // Allocate new matrix of the same dimensions.

    uint256 ptr;

    assembly {
        // Making a big assumption here that `data` uint8[3] entries
        // are laid out contiguously in memory right after the pointers.
        ptr := mload(data)
    }

    C = mallocM32x32(3, 3); // Allocate memory for matrix.

    fromUintPtrTo_(ptr, C); // Copy words from `ptr` to packed `C`.
}

function fromUintArray(uint8[4][2] memory data) pure returns (M32x32 C) {
    uint256 ptr;

    assembly {
        ptr := mload(data)
    }

    C = mallocM32x32(2, 4); // Allocate memory for matrix.

    fromUintPtrTo_(ptr, C); // Copy words from `ptr` to packed `C`.
}

function fromUintArray(uint8[4][4] memory data) pure returns (M32x32 C) {
    uint256 ptr;

    assembly {
        ptr := mload(data)
    }

    C = mallocM32x32(4, 4); // Allocate memory for matrix.

    fromUintPtrTo_(ptr, C); // Copy words from `ptr` to packed `C`.
}

function fromUintArray(uint256[2][2] memory data) pure returns (M32x32 C) {
    uint256 ptr;

    assembly {
        ptr := mload(data)
    }

    C = mallocM32x32(2, 2); // Allocate memory for matrix.

    fromUintPtrTo_(ptr, C); // Copy words from `ptr` to packed `C`.
}

function fromUintArray(uint256[3][3] memory data) pure returns (M32x32 C) {
    uint256 ptr;

    assembly {
        ptr := mload(data)
    }

    C = mallocM32x32(3, 3); // Allocate memory for matrix.

    fromUintPtrTo_(ptr, C); // Copy words from `ptr` to packed `C`.
}

function fromUintPtr(uint256 ptr, uint256 n, uint256 m) pure returns (M32x32 C) {
    C = mallocM32x32(n, m);

    fromUintPtrTo_(ptr, C);
}

function fromUint256PtrToUnsafe_(uint256 ptr, M32x32 C) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrC) = header(C);
        // Loop over all `n * m` elements of 32 bytes.
        uint256 size = n * m * 32;
        // Up until here we can load & parse full words (4 elements).
        uint256 end = ptr + (size & ~uint256(127));
        // The rest needs to be parsed individually.
        uint256 rest = size & 127;

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
                let aX4 := shl(224, mload(ptr))
                aX4 := or(aX4, shl(160, mload(add(0x20, ptr))))
                aX4 := or(aX4, shl(96, mload(add(0x40, ptr))))
                aX4 := or(aX4, shl(32, mload(add(0x60, ptr))))

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
                aX4 := or(aX4, shl(128, mload(add(0x20, ptr))))
                aX4 := or(aX4, shl(64, mload(add(0x40, ptr))))

                mstore(ptrC, and(aX4, mask)) // Store packed `c` in `ptrC`.
            }
        }
    }
}

function packWordUnsafe(N32x32 a, N32x32 b, N32x32 c, N32x32 d) pure returns (uint256 word) {
    word = (uint256(uint64(N32x32.unwrap(a))) << 192) | (uint256(uint64(N32x32.unwrap(b))) << 128)
        | (uint256(uint64(N32x32.unwrap(c))) << 64) | (uint256(uint64(N32x32.unwrap(d))));
}

function packWordUnsafe(uint256 a, uint256 b, uint256 c, uint256 d) pure returns (uint256 word) {
    word = (a << 192) | (b << 128) | (c << 64) | d;
}
