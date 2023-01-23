// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "./UM256.sol" as __UM256;
import "./N32x32.sol" as __N32x32;
import {N32x32} from "./N32x32.sol";

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
    bytes_,
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
    mulScalar,
    mulScalarTo_,
    mulScalarUnchecked,
    mulScalarUncheckedTo_,
    dot,
    dotTransposed,
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

uint256 constant _UINT64_MAX = 0xffffffffffffffff;
uint256 constant _UINT32_MAX = 0xffffffff;
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

    if ((n | m | (ptr >> 40)) > __UM256.MAX_24_BITS) revert M32x32_TooLarge();
}

function header(M32x32 A) pure returns (uint256 n, uint256 m, uint256 ptr) {
    n = (M32x32.unwrap(A)) & __UM256.MAX_24_BITS;
    m = (M32x32.unwrap(A) >> 24) & __UM256.MAX_24_BITS;
    ptr = (M32x32.unwrap(A) >> 48) & _UINT64_MAX;
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
        uint256 diagSpacing = 8 + n * 8;
        // Loop over all `n` diagonal elements.
        uint256 end = ptr + n * diagSpacing;

        if (ptr != end) {
            assembly {
                let preserveWord := and(mload(ptr), not(_UINT64_MAX))

                mstore(ptr, or(1, preserveWord)) // Store `1` at `ptr`, preserve existing word.
            }

            ptr = ptr + diagSpacing; // Advance pointer to the next slot in the diagonal.
        }

        while (ptr != end) {
            assembly {
                mstore(ptr, 1) // Store `1` at `ptr`, preserve existing word.
            }

            ptr = ptr + diagSpacing; // Advance pointer to the next slot in the diagonal.
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
            uint256 preserveWord = packWordUnsafe(a, a + 1, a + 2, a + 3);

            assembly {
                mstore(ptr, preserveWord) // Store `a` at current pointer location.
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
            let preserveWord := and(mload(ptr), not(_UINT64_MAX))

            mstore(ptr, or(value, preserveWord))
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
            let preserveWord := and(mload(ptr), not(_UINT64_MAX))

            mstore(ptr, or(value, preserveWord))
        }
    }
}

function setUnsafe(M32x32 A, uint256 i, uint256 j, uint256 value) pure {
    unchecked {
        (, uint256 m, uint256 ptr) = header(A);

        ptr = ptr + 8 * (uint256(i) * m + uint256(j) - 3);

        assembly {
            let preserveWord := and(mload(ptr), not(_UINT64_MAX))

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
                let a := and(mload(ptrA), mask) // Load packed values from `A` at `ptrA`.
                let b := and(mload(ptrB), mask) // Load packed values from `B` at `ptrB`.
                let c := add(a, b) // Add packed values together.

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
                let c := add(a, b) // Add packed values together.

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

        uint256 ptrBjEnd = dataPtrB + (ptrBRowSize & ~uint256(31));
        uint256 ptrBjRest = ptrBRowSize & 31;
        uint256 ptrBj;

        // Loop over `A`s `i` indices (rows).
        while (ptrAi != ptrAiEnd) {
            // i-loop start.

            ptrBj = dataPtrB;

            // Loop over `B`s `j` indices (cols).
            while (ptrBj != ptrBjEnd) {
                // j-loop start.

                uint256 ptrBkj = ptrBj;
                uint256 ptrAik = ptrAi;
                // End inner loop after one row of `A`.
                // Up until here we can load & parse full words (4 elements).
                uint256 ptrAikEnd = ptrAi + (ptrARowSize & ~uint256(31));
                // The rest needs to be parsed individually.
                uint256 ptrAikRest = ptrARowSize & 31;

                // Perform the dot product on the current
                // row vector `Ai` and the column vector `Bj`.
                // Store the result in `c`.
                uint256 cX4;

                // Loop over `A`s cols and `B`s rows in strides of 4.
                while (ptrAik != ptrAikEnd) {
                    // k-loop start.

                    assembly {
                        let aX4 := mload(ptrAik) // Load packed A[i:i+4,k].

                        let b1X4 := mload(ptrBkj) // Load packed B[k+0,j:j+4].
                        ptrBkj := add(ptrBkj, ptrBRowSize) // Advance to the next row ↓ of `B`.
                        let b2X4 := mload(ptrBkj) // Load packed B[k+1,j:j+4].
                        ptrBkj := add(ptrBkj, ptrBRowSize) // Advance to the next row ↓ of `B`.
                        let b3X4 := mload(ptrBkj) // Load packed B[k+2,j:j+4].
                        ptrBkj := add(ptrBkj, ptrBRowSize) // Advance to the next row ↓ of `B`.
                        let b4X4 := mload(ptrBkj) // Load packed B[k+3,j:j+4].
                        ptrBkj := add(ptrBkj, ptrBRowSize) // Advance to the next row ↓ of `B`.

                        cX4 := add(cX4, mul(shr(192, aX4), b1X4))
                        cX4 := add(cX4, mul(and(shr(128, aX4), _UINT64_MAX), b2X4))
                        cX4 := add(cX4, mul(and(shr(64, aX4), _UINT64_MAX), b3X4))
                        cX4 := add(cX4, mul(and(aX4, _UINT64_MAX), b4X4))
                    }

                    ptrAik = ptrAik + 32; // Advance to the next column → of `A` in strides of 4.
                }

                // Parse the last remaining word.
                if (ptrAikRest != 0) {
                    assembly {
                        // Mask applies to leftover bits in word.
                        let mask := not(shr(mul(ptrAikRest, 8), not(0)))
                        let aX4 := and(mload(ptrAik), mask) // Load packed values from `A` at `ptrA`.

                        let b1X4 := mload(ptrBkj) // Load packed B[k+0,j:j+4].
                        ptrBkj := add(ptrBkj, ptrBRowSize) // Advance to the next row ↓ of `B`.
                        let b2X4 := mload(ptrBkj) // Load packed B[k+1,j:j+4].
                        ptrBkj := add(ptrBkj, ptrBRowSize) // Advance to the next row ↓ of `B`.
                        let b3X4 := mload(ptrBkj) // Load packed B[k+2,j:j+4].
                        ptrBkj := add(ptrBkj, ptrBRowSize) // Advance to the next row ↓ of `B`.

                        cX4 := add(cX4, mul(shr(192, aX4), and(b1X4, mask)))
                        cX4 := add(cX4, mul(and(shr(128, aX4), _UINT64_MAX), and(b2X4, mask)))
                        cX4 := add(cX4, mul(and(shr(64, aX4), _UINT64_MAX), and(b3X4, mask)))
                    }
                }

                assembly {
                    mstore(ptrCij, cX4) // Store the packed result in C[i:i+4,j].
                }

                ptrCij = ptrCij + 32; // Advance to the next element of `C` in strides of 4.
                ptrBj = ptrBj + 32; // Advance to the next column → of `B` in strides of 4.
            }

            if (ptrBjRest != 0) {
                // Repeat the while-loop and apply masking.
                uint256 maskBj;
                assembly {
                    // Mask applies to leftover bits in word.
                    maskBj := not(shr(mul(ptrBjRest, 8), not(0)))
                }

                uint256 ptrBkj = ptrBj;
                uint256 ptrAik = ptrAi;
                // End inner loop after one row of `A`.
                // Up until here we can load & parse full words (4 elements).
                uint256 ptrAikEnd = ptrAi + (ptrARowSize & ~uint256(31));
                // // The rest needs to be parsed individually.
                // uint256 ptrAikRest = ptrARowSize & 31;

                // Perform the dot product on the current
                // row vector `Ai` and the column vector `Bj`.
                // Store the result in `c`.
                uint256 cX4;

                // Loop over `A`s cols and `B`s rows in strides of 4.
                while (ptrAik != ptrAikEnd) {
                    // k-loop start.

                    assembly {
                        let aX4 := mload(ptrAik) // Load packed A[i,k].

                        let b1X4 := and(mload(ptrBkj), maskBj) // Load packed B[k,j].
                        ptrBkj := add(ptrBkj, ptrBRowSize) // Advance to the next row ↓ of `B`.
                        let b2X4 := and(mload(ptrBkj), maskBj) // Load packed B[k,j].
                        ptrBkj := add(ptrBkj, ptrBRowSize) // Advance to the next row ↓ of `B`.
                        let b3X4 := and(mload(ptrBkj), maskBj) // Load packed B[k,j].
                        ptrBkj := add(ptrBkj, ptrBRowSize) // Advance to the next row ↓ of `B`.
                        let b4X4 := and(mload(ptrBkj), maskBj) // Load packed B[k,j].
                        ptrBkj := add(ptrBkj, ptrBRowSize) // Advance to the next row ↓ of `B`.

                        cX4 := add(cX4, mul(shr(192, aX4), b1X4))
                        cX4 := add(cX4, mul(and(shr(128, aX4), _UINT64_MAX), b2X4))
                        cX4 := add(cX4, mul(and(shr(64, aX4), _UINT64_MAX), b3X4))
                        cX4 := add(cX4, mul(and(aX4, _UINT64_MAX), b4X4))
                    }

                    ptrAik = ptrAik + 32; // Advance to the next column → of `A` in strides of 4.
                }

                // Parse the last remaining word.
                if (ptrARowSize & 31 != 0) {
                    assembly {
                        // Mask applies to leftover bits in word.
                        let mask := not(shr(mul(and(ptrARowSize, 31), 8), not(0)))
                        let aX4 := and(mload(ptrAik), mask) // Load packed values from `A` at `ptrA`.

                        let b1X4 := and(mload(ptrBkj), maskBj) // Load packed B[k,j].
                        ptrBkj := add(ptrBkj, ptrBRowSize) // Advance to the next row ↓ of `B`.
                        let b2X4 := and(mload(ptrBkj), maskBj) // Load packed B[k,j].
                        ptrBkj := add(ptrBkj, ptrBRowSize) // Advance to the next row ↓ of `B`.
                        let b3X4 := and(mload(ptrBkj), maskBj) // Load packed B[k,j].

                        cX4 := add(cX4, mul(shr(192, aX4), and(b1X4, mask)))
                        cX4 := add(cX4, mul(and(shr(128, aX4), _UINT64_MAX), and(b2X4, mask)))
                        cX4 := add(cX4, mul(and(shr(64, aX4), _UINT64_MAX), and(b3X4, mask)))
                    }
                }

                assembly {
                    mstore(ptrCij, cX4) // Store the packed result in C[i,j].
                }

                ptrCij = ptrCij + (ptrBjRest & 31); // Advance to the next row ↓ of `C`.
            }

            ptrAi = ptrAi + ptrARowSize; // Advance to the next row ↓ of `A`.
        }
    }
}

/// @dev Computes `C_ij = A_ik B_jk`
function dotTransposedX4(M32x32 A, M32x32 B) pure returns (M32x32 C) {
    unchecked {
        (uint256 nA, uint256 mA, uint256 dataPtrA) = header(A);
        (uint256 nB, uint256 mB, uint256 dataPtrB) = header(B);

        if (mA != mB) revert M32x32_IncompatibleDimensions();

        C = mallocM32x32(nA, nB);

        // Offset pointer by 3 (of 4) 8 byte chunks.
        // This way the loaded values will be right-aligned.
        uint256 ptrCij = ref(C);

        uint256 ptrARowSize = 8 * mA;
        uint256 ptrBRowSize = 8 * mB;

        uint256 ptrAiEnd = dataPtrA + 8 * nA * mA;
        uint256 ptrAi = dataPtrA; // Updates by row size of `A` in i-loop.

        // // Up until here we can load & parse full words (4 elements).
        // uint256 ptrBjEnd = dataPtrB + (ptrBRowSize & ~uint256(31));
        // // The rest needs to be parsed individually.
        // uint256 ptrBjRest = ptrBRowSize & 31;
        uint256 ptrBjEnd = dataPtrB + 8 * nB * mB;
        uint256 ptrBj;

        // Loop over `A`s `i` indices (rows).
        while (ptrAi != ptrAiEnd) {
            // i-loop start.

            ptrBj = dataPtrB;

            // Loop over `B`s `j` indices (rows).
            while (ptrBj != ptrBjEnd) {
                // j-loop start.

                uint256 l;
                // Perform the dot product on the current
                // row vector `Ai` and the row vector `Bj`.
                // Store the result in `c`.
                uint256 cX4;

                while (true) {
                    uint256 ptrBjk = ptrBj;
                    uint256 ptrAik = ptrAi;
                    // End inner loop after one row of `A`.
                    // Up until here we can load & parse full words (4 elements).
                    uint256 ptrAikEnd = ptrAi + (ptrARowSize & ~uint256(31));
                    // The rest needs to be parsed individually.
                    uint256 ptrAikRest = ptrARowSize & 31;

                    // Loop over `A`s cols and `B`s cols in strides of 4.
                    while (ptrAik != ptrAikEnd) {
                        // k-loop start.

                        assembly {
                            let aX4 := mload(ptrAik) // Load packed A[i,k].
                            let bX4 := mload(ptrBjk) // Load packed B[j,k].

                            cX4 := add(cX4, mul(and(aX4, _UINT64_MAX), and(bX4, _UINT64_MAX)))
                            cX4 := add(cX4, mul(and(shr(64, aX4), _UINT64_MAX), and(shr(64, bX4), _UINT64_MAX)))
                            cX4 := add(cX4, mul(and(shr(128, aX4), _UINT64_MAX), and(shr(128, bX4), _UINT64_MAX)))
                            cX4 := add(cX4, mul(shr(192, aX4), shr(192, bX4)))
                        }

                        ptrAik = ptrAik + 32; // Advance to the next column → of `A` in strides of 4.
                        ptrBjk = ptrBjk + 32; // Advance to the next column → of `B` in strides of 4.
                    }

                    // Parse the last remaining word.
                    if (ptrAikRest != 0) {
                        assembly {
                            // Mask applies to leftover bits in word.
                            let mask := not(shr(mul(ptrAikRest, 8), not(0)))
                            let aX4 := and(mload(ptrAik), mask) // Load packed values from `A` at `ptrA`.
                            let bX4 := and(mload(ptrBjk), mask) // Load packed values from `B` at `ptrB`.

                            cX4 := add(cX4, mul(and(shr(64, aX4), _UINT64_MAX), and(shr(64, bX4), _UINT64_MAX)))
                            cX4 := add(cX4, mul(and(shr(128, aX4), _UINT64_MAX), and(shr(128, bX4), _UINT64_MAX)))
                            cX4 := add(cX4, mul(shr(192, aX4), shr(192, bX4)))
                        }
                    }

                    ptrBj = ptrBj + ptrBRowSize; // Advance to the next row ↓ of `B`.

                    if (l == 3) break;

                    l = l + 1;
                    cX4 = cX4 << 64;
                }

                assembly {
                    // // Preserve the previous data in memory.
                    // let word := and(mload(ptrCij), not(_UINT64_MAX))

                    mstore(ptrCij, cX4) // Store the result in C[i,j].
                }

                ptrCij = ptrCij + 32; // Advance to the next element of `C` in strides of 4.
            }

            ptrAi = ptrAi + ptrARowSize; // Advance to the next row ↓ of `A`.
        }
    }
}

function dotX4(M32x32 A, M32x32 B) pure returns (M32x32 C) {
    unchecked {
        (uint256 nA, uint256 mA, uint256 dataPtrA) = header(A);
        (uint256 nB, uint256 mB, uint256 dataPtrB) = header(B);

        if (mA != nB) revert M32x32_IncompatibleDimensions();
        if ((mB | mA) & 3 != 0) revert M32x32_DimensionsNotDivisibleBy4();

        C = mallocM32x32(nA, mB);

        uint256 ptrCij = ref(C);

        uint256 ptrARowSize = 8 * mA;
        uint256 ptrBRowSize = 8 * mB;

        uint256 ptrAiEnd = dataPtrA + 8 * nA * mA;
        uint256 ptrAi = dataPtrA; // Updates by row size of `A` in i-loop.

        uint256 ptrBjEnd = dataPtrB + ptrBRowSize;
        uint256 ptrBj;

        // Loop over `A`s `i` indices (rows).
        while (ptrAi != ptrAiEnd) {
            // i-loop start.

            ptrBj = dataPtrB;

            // Loop over `B`s `j` indices (cols).
            while (ptrBj != ptrBjEnd) {
                // j-loop start.

                uint256 ptrBkj = ptrBj;
                uint256 ptrAik = ptrAi;
                // End inner loop after one row of `A`.
                uint256 ptrAikEnd = ptrAi + ptrARowSize;

                // Perform the dot product on the current
                // row vector `Ai` and the column vector `Bj`.
                // Store the result in packed `c`.
                uint256 cX4;

                // Loop over `A`s cols and `B`s rows in strides of 4.
                while (ptrAik != ptrAikEnd) {
                    // k-loop start.

                    assembly {
                        let aX4 := mload(ptrAik) // Load packed A[i,k].

                        let b1X4 := mload(ptrBkj) // Load packed B[k,j].
                        ptrBkj := add(ptrBkj, ptrBRowSize) // Advance to the next row ↓ of `B`.
                        let b2X4 := mload(ptrBkj) // Load packed B[k,j].
                        ptrBkj := add(ptrBkj, ptrBRowSize) // Advance to the next row ↓ of `B`.
                        let b3X4 := mload(ptrBkj) // Load packed B[k,j].
                        ptrBkj := add(ptrBkj, ptrBRowSize) // Advance to the next row ↓ of `B`.
                        let b4X4 := mload(ptrBkj) // Load packed B[k,j].
                        ptrBkj := add(ptrBkj, ptrBRowSize) // Advance to the next row ↓ of `B`.

                        cX4 := add(cX4, mul(shr(192, aX4), b1X4))
                        cX4 := add(cX4, mul(and(shr(128, aX4), _UINT64_MAX), b2X4))
                        cX4 := add(cX4, mul(and(shr(64, aX4), _UINT64_MAX), b3X4))
                        cX4 := add(cX4, mul(and(aX4, _UINT64_MAX), b4X4))
                    }

                    ptrAik = ptrAik + 32; // Advance to the next column → of `A` in strides of 4.
                }

                assembly {
                    mstore(ptrCij, cX4) // Store the packed result in C[i,j].
                }

                ptrCij = ptrCij + 32; // Advance to the next element of `C` in strides of 4.
                ptrBj = ptrBj + 32; // Advance to the next column → of `B` in strides of 4.
            }

            ptrAi = ptrAi + ptrARowSize; // Advance to the next row ↓ of `A`.
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

        // Offset pointer by 3 (of 4) 8 byte chunks.
        // This way the loaded values will be right-aligned.
        uint256 ptrCij = ref(C) - 24;

        uint256 ptrARowSize = 8 * mA;
        uint256 ptrBRowSize = 8 * mB;

        uint256 ptrAiEnd = dataPtrA + 8 * nA * mA;
        uint256 ptrAi = dataPtrA; // Updates by row size of `A` in i-loop.

        // // Up until here we can load & parse full words (4 elements).
        // uint256 ptrBjEnd = dataPtrB + (ptrBRowSize & ~uint256(31));
        // // The rest needs to be parsed individually.
        // uint256 ptrBjRest = ptrBRowSize & 31;
        uint256 ptrBjEnd = dataPtrB + 8 * nB * mB;
        uint256 ptrBj;

        // Loop over `A`s `i` indices (rows).
        while (ptrAi != ptrAiEnd) {
            // i-loop start.

            ptrBj = dataPtrB;

            // Loop over `B`s `j` indices (rows).
            while (ptrBj != ptrBjEnd) {
                // j-loop start.

                uint256 ptrBjk = ptrBj;
                uint256 ptrAik = ptrAi;
                // End inner loop after one row of `A`.
                // Up until here we can load & parse full words (4 elements).
                uint256 ptrAikEnd = ptrAi + (ptrARowSize & ~uint256(31));
                // The rest needs to be parsed individually.
                uint256 ptrAikRest = ptrARowSize & 31;

                // Perform the dot product on the current
                // row vector `Ai` and the row vector `Bj`.
                // Store the result in `c`.
                uint256 c;

                // Loop over `A`s cols and `B`s cols in strides of 4.
                while (ptrAik != ptrAikEnd) {
                    // k-loop start.

                    assembly {
                        let aX4 := mload(ptrAik) // Load packed A[i,k].
                        let bX4 := mload(ptrBjk) // Load packed B[j,k].

                        c := add(c, mul(and(aX4, _UINT64_MAX), and(bX4, _UINT64_MAX)))
                        c := add(c, mul(and(shr(64, aX4), _UINT64_MAX), and(shr(64, bX4), _UINT64_MAX)))
                        c := add(c, mul(and(shr(128, aX4), _UINT64_MAX), and(shr(128, bX4), _UINT64_MAX)))
                        c := add(c, mul(shr(192, aX4), shr(192, bX4)))
                    }

                    ptrAik = ptrAik + 32; // Advance to the next column → of `A` in strides of 4.
                    ptrBjk = ptrBjk + 32; // Advance to the next column → of `B` in strides of 4.
                }

                // Parse the last remaining word.
                if (ptrAikRest != 0) {
                    assembly {
                        // Mask applies to leftover bits in word.
                        let mask := not(shr(mul(ptrAikRest, 8), not(0)))
                        let aX4 := and(mload(ptrAik), mask) // Load packed values from `A` at `ptrA`.
                        let bX4 := and(mload(ptrBjk), mask) // Load packed values from `B` at `ptrB`.

                        c := add(c, mul(and(shr(64, aX4), _UINT64_MAX), and(shr(64, bX4), _UINT64_MAX)))
                        c := add(c, mul(and(shr(128, aX4), _UINT64_MAX), and(shr(128, bX4), _UINT64_MAX)))
                        c := add(c, mul(shr(192, aX4), shr(192, bX4)))
                    }
                }

                assembly {
                    // Preserve the previous data in memory.
                    let word := and(mload(ptrCij), not(_UINT64_MAX))

                    mstore(ptrCij, or(word, c)) // Store the result in C[i,j].
                }

                ptrCij = ptrCij + 8; // Advance to the next element of `C`.
                ptrBj = ptrBj + ptrBRowSize; // Advance to the next row ↓ of `B`.
            }

            ptrAi = ptrAi + ptrARowSize; // Advance to the next row ↓ of `A`.
        }
    }
}

// /// @dev Computes `C_ij = A_ik B_jk`
// function dotTransposedX4(M32x32 A, M32x32 B) pure returns (M32x32 C) {
//     unchecked {
//         (uint256 nA, uint256 mA, uint256 dataPtrA) = header(A);
//         (uint256 nB, uint256 mB, uint256 dataPtrB) = header(B);

//         if (mA != mB) revert M32x32_IncompatibleDimensions();

//         C = mallocM32x32(nA, nB);

//         // Offset pointer by 3 (of 4) 8 byte chunks.
//         // This way the loaded values will be right-aligned.
//         uint256 ptrCij = ref(C);

//         uint256 ptrARowSize = 8 * mA;
//         uint256 ptrBRowSize = 8 * mB;

//         uint256 ptrAiEnd = dataPtrA + 8 * nA * mA;
//         uint256 ptrAi = dataPtrA; // Updates by row size of `A` in i-loop.

//         // // Up until here we can load & parse full words (4 elements).
//         // uint256 ptrBjEnd = dataPtrB + (ptrBRowSize & ~uint256(31));
//         // // The rest needs to be parsed individually.
//         // uint256 ptrBjRest = ptrBRowSize & 31;
//         uint256 ptrBjEnd = dataPtrB + 8 * nB * mB;
//         uint256 ptrBj;

//         // Loop over `A`s `i` indices (rows).
//         while (ptrAi != ptrAiEnd) {
//             // i-loop start.

//             ptrBj = dataPtrB;

//             // Loop over `B`s `j` indices (rows).
//             while (ptrBj != ptrBjEnd) {
//                 // j-loop start.

//                 uint256 l;
//                 // Perform the dot product on the current
//                 // row vector `Ai` and the row vector `Bj`.
//                 // Store the result in `c`.
//                 uint256 cX4;

//                 while (true) {
//                     uint256 ptrBjk = ptrBj;
//                     uint256 ptrAik = ptrAi;
//                     // End inner loop after one row of `A`.
//                     // Up until here we can load & parse full words (4 elements).
//                     uint256 ptrAikEnd = ptrAi + (ptrARowSize & ~uint256(31));
//                     // The rest needs to be parsed individually.
//                     uint256 ptrAikRest = ptrARowSize & 31;

//                     // Loop over `A`s cols and `B`s cols in strides of 4.
//                     while (ptrAik != ptrAikEnd) {
//                         // k-loop start.

//                         assembly {
//                             let aX4 := mload(ptrAik) // Load packed A[i,k].
//                             let bX4 := mload(ptrBjk) // Load packed B[j,k].

//                             cX4 := add(cX4, mul(and(aX4, _UINT64_MAX), and(bX4, _UINT64_MAX)))
//                             cX4 := add(cX4, mul(and(shr(64, aX4), _UINT64_MAX), and(shr(64, bX4), _UINT64_MAX)))
//                             cX4 := add(cX4, mul(and(shr(128, aX4), _UINT64_MAX), and(shr(128, bX4), _UINT64_MAX)))
//                             cX4 := add(cX4, mul(shr(192, aX4), shr(192, bX4)))
//                         }

//                         ptrAik = ptrAik + 32; // Advance to the next column → of `A` in strides of 4.
//                         ptrBjk = ptrBjk + 32; // Advance to the next column → of `B` in strides of 4.
//                     }

//                     // Parse the last remaining word.
//                     if (ptrAikRest != 0) {
//                         assembly {
//                             // Mask applies to leftover bits in word.
//                             let mask := not(shr(mul(ptrAikRest, 8), not(0)))
//                             let aX4 := and(mload(ptrAik), mask) // Load packed values from `A` at `ptrA`.
//                             let bX4 := and(mload(ptrBjk), mask) // Load packed values from `B` at `ptrB`.

//                             cX4 := add(cX4, mul(and(shr(64, aX4), _UINT64_MAX), and(shr(64, bX4), _UINT64_MAX)))
//                             cX4 := add(cX4, mul(and(shr(128, aX4), _UINT64_MAX), and(shr(128, bX4), _UINT64_MAX)))
//                             cX4 := add(cX4, mul(shr(192, aX4), shr(192, bX4)))
//                         }
//                     }

//                     ptrBj = ptrBj + ptrBRowSize; // Advance to the next row ↓ of `B`.

//                     if (l == 3) break;

//                     l = l + 1;
//                     cX4 = cX4 << 64;
//                 }

//                 assembly {
//                     // // Preserve the previous data in memory.
//                     // let word := and(mload(ptrCij), not(_UINT64_MAX))

//                     mstore(ptrCij, cX4) // Store the result in C[i,j].
//                 }

//                 ptrCij = ptrCij + 32; // Advance to the next element of `C` in strides of 4.
//             }

//             ptrAi = ptrAi + ptrARowSize; // Advance to the next row ↓ of `A`.
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
        // Up until here we can load & parse full words (4 elements).
        uint256 endA = ptrA + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = size & 31;
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
        // Up until here we can load & parse full words (4 elements).
        uint256 endA = ptrA + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = size & 31;
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

function min(M32x32 A) pure returns (uint256 minValue) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        minValue = type(uint256).max; // Set current min to `type(uint256).max`.

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

                let a := and(aX4, _UINT64_MAX)
                if lt(a, minValue) { minValue := a } // Check whether `a < minValue`.
                aX4 := shr(64, aX4)
                a := and(aX4, _UINT64_MAX)
                if lt(a, minValue) { minValue := a } // Check whether `a < minValue`.
                aX4 := shr(64, aX4)
                a := and(aX4, _UINT64_MAX)
                if lt(a, minValue) { minValue := a } // Check whether `a < minValue`.
                aX4 := shr(64, aX4)
                a := aX4
                if lt(a, minValue) { minValue := a } // Check whether `a < minValue`.
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
                uint256 a = (aX4 >> ((32 - rest) * 8)) & _UINT64_MAX;

                if (a < minValue) minValue = a;

                rest = rest - 8;
            }
        }
    }
}

function max(M32x32 A) pure returns (uint256 maxValue) {
    unchecked {
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

                let a := and(aX4, _UINT64_MAX)
                if gt(a, maxValue) { maxValue := a } // Check whether `a > maxValue`.
                aX4 := shr(64, aX4)
                a := and(aX4, _UINT64_MAX)
                if gt(a, maxValue) { maxValue := a } // Check whether `a > maxValue`.
                aX4 := shr(64, aX4)
                a := and(aX4, _UINT64_MAX)
                if gt(a, maxValue) { maxValue := a } // Check whether `a > maxValue`.
                aX4 := shr(64, aX4)
                a := aX4
                if gt(a, maxValue) { maxValue := a } // Check whether `a > maxValue`.
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
                uint256 a = (aX4 >> ((32 - rest) * 8)) & _UINT64_MAX;

                if (a > maxValue) maxValue = a;

                rest = rest - 8;
            }
        }
    }
}

function minMax(M32x32 A) pure returns (uint256 minValue, uint256 maxValue) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        minValue = type(uint256).max; // Set current min to `type(uint256).max`.

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

                let a := and(aX4, _UINT64_MAX)
                if lt(a, minValue) { minValue := a } // Check whether `a < minValue`.
                if gt(a, maxValue) { maxValue := a } // Check whether `a > maxValue`.
                aX4 := shr(64, aX4)
                a := and(aX4, _UINT64_MAX)
                if lt(a, minValue) { minValue := a } // Check whether `a < minValue`.
                if gt(a, maxValue) { maxValue := a } // Check whether `a > maxValue`.
                aX4 := shr(64, aX4)
                a := and(aX4, _UINT64_MAX)
                if lt(a, minValue) { minValue := a } // Check whether `a < minValue`.
                if gt(a, maxValue) { maxValue := a } // Check whether `a > maxValue`.
                aX4 := shr(64, aX4)
                a := aX4
                if lt(a, minValue) { minValue := a } // Check whether `a < minValue`.
                if gt(a, maxValue) { maxValue := a } // Check whether `a > maxValue`.
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
                uint256 a = (aX4 >> ((32 - rest) * 8)) & _UINT64_MAX;

                if (a < minValue) minValue = a;
                if (a > maxValue) maxValue = a;

                rest = rest - 8;
            }
        }
    }
}

function sum(M32x32 A) pure returns (uint256 s) {
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
                s := add(s, and(aX4, _UINT64_MAX))
                s := add(s, and(shr(64, aX4), _UINT64_MAX))
                s := add(s, and(shr(128, aX4), _UINT64_MAX))
                s := add(s, shr(192, aX4))
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
                uint256 a = (aX4 >> ((32 - rest) * 8)) & _UINT64_MAX;

                s = s + a;
                rest = rest - 8;
            }
        }
    }
}

function mean(M32x32 A) pure returns (uint256 s) {
    unchecked {
        (uint256 n, uint256 m) = shape(A);

        return sum(A) / (n * m);
    }
}

// https://en.wikipedia.org/wiki/Algorithms_for_calculating_variance#Computing_shifted_data
function vari(M32x32 A) pure returns (uint256 variance) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        uint256 len = n * m;

        if (len < 2) return 0;

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
                let a := and(aX4, _UINT64_MAX)
                s := add(s, a)
                s2 := add(s2, mul(a, a))

                a := and(shr(64, aX4), _UINT64_MAX)
                s := add(s, a)
                s2 := add(s2, mul(a, a))

                a := and(shr(128, aX4), _UINT64_MAX)
                s := add(s, a)
                s2 := add(s2, mul(a, a))

                a := and(shr(192, aX4), _UINT64_MAX)
                s := add(s, a)
                s2 := add(s2, mul(a, a))
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
                uint256 a = (aX4 >> ((32 - rest) * 8)) & _UINT64_MAX;

                s = s + a;
                s2 = s2 + a * a;
                rest = rest - 8;
            }
        }

        variance = ((s2 - (s * s + (len + 1) / 2) / len) + len / 2 - 1) / (len - 1); // note: uses the unbiased version. Use `/ len` for the biased version.
    }
}

function eqAllScalar(M32x32 A, uint256 s) pure returns (bool equals) {
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

function gtAllScalar(M32x32 A, uint256 s) pure returns (bool gt) {
    if (s == type(uint256).max) return gt = false; // Exit early.

    unchecked {
        gt = gteAllScalar(A, s + 1);
    }
}

function gteAllScalar(M32x32 A, uint256 s) pure returns (bool gte) {
    unchecked {
        if (s == 0) return true; // Exit early.

        s = s - 1; // Reduce `s` so we can use `gt`.
        gte = true;

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

                gte := gt(and(aX4, _UINT64_MAX), s) // Check whether `a > s`.
                aX4 := shr(64, aX4)
                gte := and(gte, gt(and(aX4, _UINT64_MAX), s)) // Check whether `a > s`.
                aX4 := shr(64, aX4)
                gte := and(gte, gt(and(aX4, _UINT64_MAX), s)) // Check whether `a > s`.
                aX4 := shr(64, aX4)
                gte := and(gte, gt(aX4, s)) // Check whether `a > s`.
            }

            if (!gte) return gte; // Exit early.

            ptr = ptr + 32; // Advance pointer to the next slot.
        }

        if (rest != 0) {
            uint256 aX4;

            assembly {
                aX4 := mload(ptr) // Load packed elements at `ptr`.
            }

            // Parse the last remaining word in chunks of 8 bytes.
            while (rest != 0) {
                uint256 a = (aX4 >> ((32 - rest) * 8)) & _UINT64_MAX;

                gte = gte && (a > s);
                rest = rest - 8;
            }
        }
    }
}

function ltAllScalar(M32x32 A, uint256 s) pure returns (bool lt) {
    if (s == 0) return lt = false; // Exit early.

    unchecked {
        lt = lteAllScalar(A, s - 1);
    }
}

function lteAllScalar(M32x32 A, uint256 s) pure returns (bool lte) {
    unchecked {
        if (s == type(uint256).max) return true; // Exit early.

        s = s + 1; // Increase `s` so we can use `lt`.
        lte = true; // Set initial value to true.

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

                lte := lt(and(aX4, _UINT64_MAX), s) // Check whether `a < s`.
                aX4 := shr(64, aX4)
                lte := and(lte, lt(and(aX4, _UINT64_MAX), s)) // Check whether `a < s`.
                aX4 := shr(64, aX4)
                lte := and(lte, lt(and(aX4, _UINT64_MAX), s)) // Check whether `a < s`.
                aX4 := shr(64, aX4)
                lte := and(lte, lt(aX4, s)) // Check whether `a < s`.
            }

            if (!lte) return lte; // Exit early.

            ptr = ptr + 32; // Advance pointer to the next slot.
        }

        if (rest != 0) {
            uint256 aX4;

            assembly {
                aX4 := mload(ptr) // Load packed elements at `ptr`.
            }

            // Parse the last remaining word in chunks of 8 bytes.
            while (rest != 0) {
                uint256 a = (aX4 >> ((32 - rest) * 8)) & _UINT64_MAX;

                lte = lte && (a < s);
                rest = rest - 8;
            }
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

        uint256 ptrARowSize = 8 * m;
        uint256 ptrCRowSize = 8 * n;
        // End iterating over `A`s columns when arriving at the last column.
        uint256 ptrAjEnd = ptrAj + ptrARowSize;

        // Loop over `A`s rows →.
        while (ptrAj != ptrAjEnd) {
            uint256 ptrA = ptrAj; // Start at the beginning of the current column.
            uint256 ptrC = ptrCi; // Start at the beginning of the current row.
            uint256 ptrCEnd = ptrCi + ptrCRowSize; // End at the last element of the current row.

            // Loop over `C`s columns ↓.
            while (ptrC != ptrCEnd) {
                assembly {
                    let preserveWord := and(mload(ptrC), not(_UINT64_MAX))
                    let a := and(mload(ptrA), _UINT64_MAX)
                    let c := or(preserveWord, a)

                    mstore(ptrC, c) // Copy element from `A` to `C`.
                }

                ptrC = ptrC + 8; // Advance to the next column →.
                ptrA = ptrA + ptrARowSize; // Advance to the next row ↓.
            }

            ptrAj = ptrAj + 8; // Advance to the next column → of `A`.
            ptrCi = ptrCi + ptrCRowSize; // Advance to the next row ↓ of `C`.
        }
    }
}

function transpose(M32x32 A) pure returns (M32x32 C) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrAj) = header(A);

        if (n == 1 || m == 1) return C = A.reshape(m, n);

        C = mallocM32x32(m, n); // Allocate memory for matrix.

        uint256 ptrCi = ref(C);

        uint256 ptrARowSize = 8 * m;
        uint256 ptrCRowSize = 8 * n;
        // End iterating over `A`s rows ➞ when arriving at the last column.
        // uint256 ptrAjEnd = ptrAj + ptrARowSize;
        uint256 ptrAjEnd = ptrAj + (ptrARowSize & ~uint256(31));

        // Loop over `A`s rows →.
        // while (ptrAj != ptrAjEnd) {
        //     uint256 ptrA = ptrAj; // Start at the beginning of the current column.
        //     uint256 ptrC = ptrCi; // Start at the beginning of the current row.
        //     uint256 ptrCEnd = ptrCi + (ptrCRowSize & ~uint256(31)); // End at the last element of the current row.

        //     // Loop over `C`s rows →.
        //     while (ptrC != ptrCEnd) {
        //         assembly {
        //             let a1X4 := mload(ptrA) // Load packed A[i+0,j:j+4].
        //             ptrA := add(ptrA, ptrARowSize) // Advance to the next row ↓ of `A`.
        //             let a2X4 := mload(ptrA) // Load packed A[i+1,j:j+4].
        //             ptrA := add(ptrA, ptrARowSize) // Advance to the next row ↓ of `A`.
        //             let a3X4 := mload(ptrA) // Load packed A[i+2,j:j+4].
        //             ptrA := add(ptrA, ptrARowSize) // Advance to the next row ↓ of `A`.
        //             let a4X4 := mload(ptrA) // Load packed A[i+3,j:j+4].
        //             ptrA := add(ptrA, ptrARowSize) // Advance to the next row ↓ of `A`.

        //             let mask := shl(192, _UINT64_MAX)
        //             let c1X4 := and(a1X4, mask)
        //             c1X4 := or(c1X4, shr(64, and(a2X4, mask)))
        //             c1X4 := or(c1X4, shr(128, and(a3X4, mask)))
        //             c1X4 := or(c1X4, shr(192, and(a4X4, mask)))

        //             mstore(ptrC, c1X4) // Copy packed elements from `A` to `C`.

        //             mask := shl(128, _UINT64_MAX)
        //             let c2X4 := shl(64, and(a1X4, shl(128, _UINT64_MAX)))
        //             c2X4 := or(c2X4, and(a2X4, shl(128, _UINT64_MAX)))
        //             c2X4 := or(c2X4, shr(64, and(a3X4, shl(128, _UINT64_MAX))))
        //             c2X4 := or(c2X4, shr(128, and(a4X4, shl(128, _UINT64_MAX))))

        //             mstore(add(ptrC, ptrCRowSize), c2X4) // Copy packed elements from `A` to `C`.

        //             mask := shl(64, _UINT64_MAX)
        //             let c3X4 := shl(128, and(a1X4, mask))
        //             c3X4 := or(c3X4, shl(64, and(a2X4, mask)))
        //             c3X4 := or(c3X4, shr(0, and(a3X4, mask)))
        //             c3X4 := or(c3X4, shr(64, and(a4X4, mask)))

        //             mstore(add(ptrC, mul(ptrCRowSize, 2)), c3X4) // Copy packed elements from `A` to `C`.

        //             let c4X4 := shl(192, and(a1X4, _UINT64_MAX))
        //             c4X4 := or(c4X4, shl(128, and(a2X4, _UINT64_MAX)))
        //             c4X4 := or(c4X4, shl(64, and(a3X4, _UINT64_MAX)))
        //             c4X4 := or(c4X4, shr(0, and(a4X4, _UINT64_MAX)))

        //             mstore(add(ptrC, mul(ptrCRowSize, 3)), c4X4) // Copy packed elements from `A` to `C`.
        //         }

        //         ptrC = ptrC + 32; // Advance to the next column → in strides of 4.
        //     }

        //     // if (ptrCRowSize & 31 != 0) {
        //     //     assembly {
        //     //         let CRowMask := shr(mul(and(ptrCRowSize, not(31)), 32), not(0))
        //     //         CRowMask := not(0)

        //     //         let a1X4 := mload(ptrA) // Load packed A[i+0,j:j+4].
        //     //         ptrA := add(ptrA, ptrARowSize) // Advance to the next row ↓ of `A`.
        //     //         let a2X4 := mload(ptrA) // Load packed A[i+1,j:j+4].
        //     //         ptrA := add(ptrA, ptrARowSize) // Advance to the next row ↓ of `A`.
        //     //         let a3X4 := mload(ptrA) // Load packed A[i+2,j:j+4].

        //     //         let mask := shl(192, _UINT64_MAX)
        //     //         let c1X4 := and(a1X4, mask)
        //     //         c1X4 := or(c1X4, shr(64, and(a2X4, mask)))
        //     //         c1X4 := or(c1X4, shr(128, and(a3X4, mask)))

        //     //         mstore(ptrC, and(c1X4, CRowMask)) // Copy packed elements from `A` to `C`.

        //     //         mask := shl(128, _UINT64_MAX)
        //     //         let c2X4 := shl(64, and(a1X4, shl(128, _UINT64_MAX)))
        //     //         c2X4 := or(c2X4, and(a2X4, shl(128, _UINT64_MAX)))
        //     //         c2X4 := or(c2X4, shr(64, and(a3X4, shl(128, _UINT64_MAX))))

        //     //         mstore(add(ptrC, ptrCRowSize), and(c2X4, CRowMask)) // Copy packed elements from `A` to `C`.

        //     //         mask := shl(64, _UINT64_MAX)
        //     //         let c3X4 := shl(128, and(a1X4, mask))
        //     //         c3X4 := or(c3X4, shl(64, and(a2X4, mask)))
        //     //         c3X4 := or(c3X4, shr(0, and(a3X4, mask)))

        //     //         mstore(add(ptrC, mul(ptrCRowSize, 2)), and(c3X4, CRowMask)) // Copy packed elements from `A` to `C`.

        //     //         let c4X4 := shl(192, and(a1X4, _UINT64_MAX))
        //     //         c4X4 := or(c4X4, shl(128, and(a2X4, _UINT64_MAX)))
        //     //         c4X4 := or(c4X4, shl(64, and(a3X4, _UINT64_MAX)))

        //     //         mstore(add(ptrC, mul(ptrCRowSize, 3)), and(c4X4, CRowMask)) // Copy packed elements from `A` to `C`.
        //     //     }
        //     // }

        //     ptrAj = ptrAj + 32; // Advance to the next column → of `A` in strides of 4.
        //     ptrCi = ptrCi + 4 * ptrCRowSize; // Advance to the next row ↓ of `C` in strides of 4.
        //         // break;
        // }

        uint256 ptrAjRest = ptrARowSize & 31;

        if (ptrAjRest != 0) {
            uint256 ptrA = ptrAj; // Start at the beginning of the current column.
            uint256 ptrC = ptrCi; // Start at the beginning of the current row.
            uint256 ptrCEnd = ptrCi + (ptrCRowSize & ~uint256(31)); // End at the last element of the current row.

            uint256 CRowMask = ~uint256(0);
            // uint256 maskA = ~uint256(0) >> ((ptrARowSize & ~uint256(31)) * 32);
            uint256 maskA = ~uint256(0);
            // let CRowMask := shr(mul(and(ptrCRowSize, not(31)), 32), not(0))

            // Loop over `C`s rows →.
            while (ptrC != ptrCEnd) {
                assembly {
                    let a1X4 := and(mload(ptrA), maskA) // Load packed A[i+0,j:j+4].
                    ptrA := add(ptrA, ptrARowSize) // Advance to the next row ↓ of `A`.
                    let a2X4 := and(mload(ptrA), maskA) // Load packed A[i+1,j:j+4].
                    ptrA := add(ptrA, ptrARowSize) // Advance to the next row ↓ of `A`.
                    let a3X4 := and(mload(ptrA), maskA) // Load packed A[i+2,j:j+4].
                    ptrA := add(ptrA, ptrARowSize) // Advance to the next row ↓ of `A`.
                    let a4X4 := and(mload(ptrA), maskA) // Load packed A[i+3,j:j+4].
                    ptrA := add(ptrA, ptrARowSize) // Advance to the next row ↓ of `A`.

                    let mask := shl(192, _UINT64_MAX)
                    let c1X4 := and(a1X4, mask)
                    c1X4 := or(c1X4, shr(64, and(a2X4, mask)))
                    c1X4 := or(c1X4, shr(128, and(a3X4, mask)))
                    c1X4 := or(c1X4, shr(192, and(a4X4, mask)))

                    mstore(ptrC, and(c1X4, CRowMask)) // Copy packed elements from `A` to `C`.

                    mask := shl(128, _UINT64_MAX)
                    let c2X4 := shl(64, and(a1X4, shl(128, _UINT64_MAX)))
                    c2X4 := or(c2X4, and(a2X4, shl(128, _UINT64_MAX)))
                    c2X4 := or(c2X4, shr(64, and(a3X4, shl(128, _UINT64_MAX))))
                    c2X4 := or(c2X4, shr(128, and(a4X4, shl(128, _UINT64_MAX))))

                    mstore(add(ptrC, ptrCRowSize), and(c2X4, CRowMask)) // Copy packed elements from `A` to `C`.

                    mask := shl(64, _UINT64_MAX)
                    let c3X4 := shl(128, and(a1X4, mask))
                    c3X4 := or(c3X4, shl(64, and(a2X4, mask)))
                    c3X4 := or(c3X4, shr(0, and(a3X4, mask)))
                    c3X4 := or(c3X4, shr(64, and(a4X4, mask)))

                    mstore(add(ptrC, mul(ptrCRowSize, 2)), and(c3X4, CRowMask)) // Copy packed elements from `A` to `C`.

                    let c4X4 := shl(192, and(a1X4, _UINT64_MAX))
                    c4X4 := or(c4X4, shl(128, and(a2X4, _UINT64_MAX)))
                    c4X4 := or(c4X4, shl(64, and(a3X4, _UINT64_MAX)))
                    c4X4 := or(c4X4, shr(0, and(a4X4, _UINT64_MAX)))

                    mstore(add(ptrC, mul(ptrCRowSize, 3)), and(c4X4, CRowMask)) // Copy packed elements from `A` to `C`.
                }

                ptrC = ptrC + 32; // Advance to the next column → in strides of 4.
            }

            // if (ptrCRowSize & 31 != 0) {
            //     assembly {
            //         let CRowMask := shr(mul(and(ptrCRowSize, not(31)), 32), not(0))
            //         CRowMask := not(0)

            //         let a1X4 := mload(ptrA) // Load packed A[i+0,j:j+4].
            //         ptrA := add(ptrA, ptrARowSize) // Advance to the next row ↓ of `A`.
            //         let a2X4 := mload(ptrA) // Load packed A[i+1,j:j+4].
            //         ptrA := add(ptrA, ptrARowSize) // Advance to the next row ↓ of `A`.
            //         let a3X4 := mload(ptrA) // Load packed A[i+2,j:j+4].

            //         let mask := shl(192, _UINT64_MAX)
            //         let c1X4 := and(a1X4, mask)
            //         c1X4 := or(c1X4, shr(64, and(a2X4, mask)))
            //         c1X4 := or(c1X4, shr(128, and(a3X4, mask)))

            //         mstore(ptrC, and(c1X4, CRowMask)) // Copy packed elements from `A` to `C`.

            //         mask := shl(128, _UINT64_MAX)
            //         let c2X4 := shl(64, and(a1X4, shl(128, _UINT64_MAX)))
            //         c2X4 := or(c2X4, and(a2X4, shl(128, _UINT64_MAX)))
            //         c2X4 := or(c2X4, shr(64, and(a3X4, shl(128, _UINT64_MAX))))

            //         mstore(add(ptrC, ptrCRowSize), and(c2X4, CRowMask)) // Copy packed elements from `A` to `C`.

            //         mask := shl(64, _UINT64_MAX)
            //         let c3X4 := shl(128, and(a1X4, mask))
            //         c3X4 := or(c3X4, shl(64, and(a2X4, mask)))
            //         c3X4 := or(c3X4, shr(0, and(a3X4, mask)))

            //         mstore(add(ptrC, mul(ptrCRowSize, 2)), and(c3X4, CRowMask)) // Copy packed elements from `A` to `C`.

            //         let c4X4 := shl(192, and(a1X4, _UINT64_MAX))
            //         c4X4 := or(c4X4, shl(128, and(a2X4, _UINT64_MAX)))
            //         c4X4 := or(c4X4, shl(64, and(a3X4, _UINT64_MAX)))

            //         mstore(add(ptrC, mul(ptrCRowSize, 3)), and(c4X4, CRowMask)) // Copy packed elements from `A` to `C`.
            //     }
            // }
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

function fromAbiEncoded(bytes memory dataBytes) pure returns (M32x32 C) {
    unchecked {
        uint256 m = dataBytes.length / 4;

        uint256 dataPtr;

        assembly {
            dataPtr := add(32, dataBytes) // Actual data is located after length encoding.
        }

        C = M32x32Header(dataPtr, 1, m); // Generate header without allocating memory.

        fromUint256PtrTo_(dataPtr, C); // Copy words from `ptr` to packed `C`.
    }
}

function fromAbiEncodedPacked_(bytes memory dataBytes) pure returns (M32x32 C) {
    C = fromAbiEncodedPacked_(dataBytes, 1, dataBytes.length / 8);
}

function fromAbiEncodedPacked_(bytes memory dataBytes, uint256 n, uint256 m) pure returns (M32x32 C) {
    unchecked {
        if (n * m * 32 > dataBytes.length) revert M32x32_TooLarge();

        uint256 dataPtr;

        assembly {
            dataPtr := add(32, dataBytes) // Actual data is located after length encoding.
        }

        C = M32x32Header(dataPtr, n, m); // Generate header without allocating memory.
    }
}

function bytes_(M32x32 A) pure returns (bytes memory dataBytes) {
    uint256 ptr = ref(A);

    assembly {
        // This only works under the assumption that
        // we always store the size in bytes before the data.
        dataBytes := sub(ptr, 32)
    }
}

/* ------------- unsafe conversions ------------- */

function fromArray(uint8[3][3] memory data) pure returns (M32x32 C) {
    C = mallocM32x32(3, 3); // Allocate new matrix of the same dimensions.

    uint256 ptr;

    assembly {
        // Making a big assumption here that `data` uint8[3] entries
        // are laid out contiguously in memory right after the pointers.
        ptr := mload(data)
    }

    C = mallocM32x32(3, 3); // Allocate memory for matrix.

    fromUint256PtrTo_(ptr, C); // Copy words from `ptr` to packed `C`.
}

function fromArray(uint8[4][2] memory data) pure returns (M32x32 C) {
    uint256 ptr;

    assembly {
        ptr := mload(data)
    }

    C = mallocM32x32(2, 4); // Allocate memory for matrix.

    fromUint256PtrTo_(ptr, C); // Copy words from `ptr` to packed `C`.
}

function fromArray(uint8[4][4] memory data) pure returns (M32x32 C) {
    uint256 ptr;

    assembly {
        ptr := mload(data)
    }

    C = mallocM32x32(4, 4); // Allocate memory for matrix.

    fromUint256PtrTo_(ptr, C); // Copy words from `ptr` to packed `C`.
}

function fromArray(uint256[2][2] memory data) pure returns (M32x32 C) {
    uint256 ptr;

    assembly {
        ptr := mload(data)
    }

    C = mallocM32x32(2, 2); // Allocate memory for matrix.

    fromUint256PtrTo_(ptr, C); // Copy words from `ptr` to packed `C`.
}

function fromUint256PtrTo_(uint256 ptr, M32x32 C) pure {
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
}

function packWordUnsafe(N32x32 a, N32x32 b, N32x32 c, N32x32 d) pure returns (uint256 word) {
    word = (uint256(uint64(int64(N32x32.unwrap(a)))) << 192) | (uint256(uint64(int64(N32x32.unwrap(b)))) << 128)
        | (uint256(uint64(int64(N32x32.unwrap(c)))) << 64) | (uint256(uint64(int64(N32x32.unwrap(d)))));
}

function packWordUnsafe(uint256 a, uint256 b, uint256 c, uint256 d) pure returns (uint256 word) {
    word = (a << 192) | (b << 128) | (c << 64) | d;
}
