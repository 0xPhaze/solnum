// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "forge-std/Test.sol";
import "./UM256.sol" as UM256Lib;

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
    addScalarUnchecked,
    mulScalarUnchecked,
    add,
    dot,
    eq,
    eqScalar,
    sum
} for M32x32 global;

error M32x32_TooLarge();
error M32x32_InvalidRange();
error M32x32_IndexOutOfBounds();
error M32x32_InvalidDimensions();
error M32x32_IncompatibleDimensions();

uint256 constant MAX_64_BITS = 0xffffffffffffffff;

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
    ptr = (M32x32.unwrap(A) >> 48) & UM256Lib.MAX_64_BITS;
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
    ptr = (M32x32.unwrap(A) >> 48) & UM256Lib.MAX_64_BITS;
}

/* ------------- constructors ------------- */

function zerosUnsafe(uint256 n, uint256 m) pure returns (M32x32 A) {
    unchecked {
        // Memory size in bytes.
        uint256 size = n * m * 8;
        // Round up the size allocated in memory to 32 bytes.
        uint256 msize = (size + 31) & (~uint256(31));
        // Allocate memory space for matrix.
        // Add 32 bytes to store the byte size.
        uint256 ptr = UM256Lib.malloc(32 + msize);

        assembly {
            // Store the bytes size.
            mstore(ptr, size)
        }

        // Generate metadata header, skip the 32 bytes length.
        // This is only for convenience when converting to `bytes`.
        A = M32x32Header(ptr + 32, n, m);
    }
}

function zeros(uint256 n, uint256 m) pure returns (M32x32 A) {
    unchecked {
        // Memory size in bytes.
        uint256 size = n * m * 8;
        // Round up the size allocated in memory to 32 bytes.
        uint256 msize = (size + 31) & ~uint256(31);
        // uint256 msize = (size + 31) >> 5 << 5;
        // uint256 msize = (size + 31) / 32 * 32;
        // Allocate memory space for matrix.
        // Add 32 bytes to store the byte size.
        uint256 ptr = UM256Lib.malloc(32 + msize);

        assembly {
            // Store the bytes size.
            mstore(ptr, size)
        }

        // Skip the 32 bytes length.
        ptr = ptr + 32;

        // Generate metadata header.
        A = M32x32Header(ptr, n, m);

        // Loop over `n * m` elements of 8 bytes.
        // 4 elements are stored per word.
        // Rounded up to slots of 32 bytes.
        uint256 end = ptr + ((n * m * 8 + 31) & ~uint256(31));

        while (ptr != end) {
            assembly {
                mstore(ptr, 0) // Store `0` at current pointer location.
            }

            ptr = ptr + 32; // Advance pointer to next slot.
        }
    }
}

// XXX note: have to shift to << 32
uint256 constant ONES_X4 = 0x1000000000000000100000000000000010000000000000001;

function ones(uint256 n, uint256 m) pure returns (M32x32 A) {
    unchecked {
        // We can unsafely allocate a new matrix,
        // because we will write to all memory slots.
        A = zerosUnsafe(n, m);

        // Obtain a reference to matrix data location.
        uint256 ptr = ref(A);

        // Loop over `n * m` elements of 8 bytes.
        uint256 end = ptr + ((n * m * 8 + 31) & ~uint256(31));

        // NOTE: if array is not divisible by 4 we are overshooting.
        while (ptr != end) {
            assembly {
                // Store `1` at current pointer location in all 4 chunks.
                mstore(ptr, ONES_X4)
            }

            ptr = ptr + 32; // Advance pointer to next slot.
        }
    }
}

function eye(uint256 n, uint256 m) pure returns (M32x32 A) {
    unchecked {
        // Only supporting square dimensions.
        if (n != m) revert M32x32_InvalidDimensions();

        // Allocate a new matrix of zeros.
        A = zeros(n, m);

        // Obtain a reference to matrix data location.
        // Offset pointer to the left by 3 chunks so that
        // the loaded chunk will be right-aligned.
        uint256 ptr = ref(A) - 24;
        // Spacing in memory between the elements on the diagonal.
        uint256 diagSpace = 8 + n * 8;
        // Loop over `n` diagonal elements.
        uint256 end = ptr + n * diagSpace;

        while (ptr != end) {
            assembly {
                let word := and(mload(ptr), not(MAX_64_BITS))

                mstore(ptr, or(1, word))
            }

            ptr = ptr + diagSpace; // Advance pointer to next slot in the diagonal.
        }
    }
}

function range(uint256 start, uint256 end) pure returns (M32x32 A) {
    unchecked {
        // `start <= end` must hold.
        if (start > end) revert M32x32_InvalidRange();

        uint256 numEl = end - start;

        // We can unsafely allocate a new matrix,
        // because we will write to all memory slots.
        A = zerosUnsafe(1, numEl);

        // Obtain a reference to matrix data location.
        // Offset pointer to the left by 3 chunks so that
        // the loaded chunk will be right-aligned.
        uint256 ptr = ref(A);

        uint256 a = start;
        uint256 aEnd = a + ((numEl + 3) & ~uint256(3));

        while (a != aEnd) {
            uint256 word = packWordUnsafe(a, a + 1, a + 2, a + 3);

            assembly {
                mstore(ptr, word) // Store `a` at current pointer location.
            }

            ptr = ptr + 32; // Advance pointer to next slot in the diagonal.
            a = a + 4;
        }
    }
}

function range(uint256 end) pure returns (M32x32 A) {
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
            a := and(mload(ptr), MAX_64_BITS)
        }
    }
}

function setIndex(M32x32 A, uint256 index, uint256 value) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        if (index >= n * m) revert M32x32_IndexOutOfBounds();

        ptr = ptr + 8 * (index - 3);

        assembly {
            let word := and(mload(ptr), not(MAX_64_BITS))

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
            a := and(mload(ptr), MAX_64_BITS)
        }
    }
}

function set(M32x32 A, uint256 i, uint256 j, uint256 value) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        if (i >= n || j >= m) revert M32x32_IndexOutOfBounds();

        ptr = ptr + 8 * (i * m + j - 3);

        assembly {
            let word := and(mload(ptr), not(MAX_64_BITS))

            mstore(ptr, or(value, word))
        }
    }
}

function setUnsafe(M32x32 A, uint256 i, uint256 j, uint256 value) pure {
    unchecked {
        (, uint256 m, uint256 ptr) = header(A);

        ptr = ptr + 8 * (uint256(i) * m + uint256(j) - 3);

        assembly {
            let word := and(mload(ptr), not(MAX_64_BITS))

            mstore(ptr, or(value, word))
        }
    }
}

/* ------------- Mat x Mat operators ------------- */

function add(M32x32 A, M32x32 B) pure returns (M32x32 C) {
    (uint256 n, uint256 m) = A.shape();

    // Allocate new matrix of the same dimensions.
    C = zerosUnsafe(n, m);

    // Add scalar `A` and `B`, store result in `C`.
    addTo_(A, B, C);
}

function addTo_(M32x32 A, M32x32 B, M32x32 C) pure {
    unchecked {
        (uint256 nA, uint256 mA, uint256 ptrA) = header(A);
        (uint256 nB, uint256 mB, uint256 ptrB) = header(B);

        if (nA != nB || mA != mB) revert M32x32_IncompatibleDimensions();

        // uint256 ptrA = dataA;
        // uint256 ptrB = dataB;
        // uint256 endA = ptrA + nA * mA * 32;
        // uint256 ptrC = ref(C);

        // Loop over `nA * mA` elements of 8 bytes.
        uint256 size = nA * mA * 8;
        // Up until here we can load & parse full words.
        uint256 endA = ptrA + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = ptrA + size - endA;
        // Obtain a reference to `C`s data location.
        uint256 ptrC = ref(C);

        while (ptrA != endA) {
            assembly {
                let a := mload(ptrA) // Load 4 values from `A` at `ptrA`.
                let b := mload(ptrB) // Load 4 values from `B` at `ptrB`.
                let c := add(a, b) // Add packed values together.

                mstore(ptrC, c) // Store packed values in `ptrC`.
            }

            // Advance pointers to next slot.
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

/// Perform the matrix multiplication given by:
/// `C_ij = A_ik B_kj`
///
/// Given `i`, `j`, `k`, the offsets
/// of the elements in `A`, `B` to be summed are:
/// `ptrA = 32 * (k + i * mA)`
/// `ptrB = 32 * (j + k * mb)`
///
/// However, it's cheaper to not keep track of `i`, `j`, `k`,
/// but to keep running pointers to the elements of the matrix.
function dot(M32x32 A, M32x32 B) pure returns (M32x32 C) {
    unchecked {
        (uint256 nA, uint256 mA, uint256 dataPtrA) = header(A);
        (uint256 nB, uint256 mB, uint256 dataPtrB) = header(B);

        if (mA != nB) revert M32x32_IncompatibleDimensions();

        C = zerosUnsafe(nA, mB);

        uint256 ptrC = ref(C);

        uint256 ptrARowSize = 32 * mA;
        uint256 ptrBRowSize = 32 * mB;

        uint256 ptrARowEnd = dataPtrA + 32 * nA * mA;
        uint256 ptrARow = dataPtrA; // Updates by row size of `A` in i-loop.

        uint256 ptrBColEnd = dataPtrB + ptrBRowSize;
        uint256 ptrBCol;

        // Loop over `C`s `i` indices.
        while (ptrARow != ptrARowEnd) {
            // i-loop start.

            ptrBCol = dataPtrB;

            while (ptrBCol != ptrBColEnd) {
                // j-loop start.

                uint256 ptrB = ptrBCol;
                uint256 ptrA = ptrARow;
                uint256 ptrAInnerEnd = ptrARow + ptrARowSize;

                // Perform the dot product on the current
                // row vector of `A` and the column vector of `B`.
                // Store the result in `c`.
                uint256 c;

                while (ptrA != ptrAInnerEnd) {
                    // k-loop start.

                    assembly {
                        let a := mload(ptrA) // Load A[i,k].
                        let b := mload(ptrB) // Load B[k,j].

                        c := add(c, mul(a, b)) // Add the product `a * b` to `c`.
                    }

                    ptrA = ptrA + 32; // Loop over `A`s columns.
                    ptrB = ptrB + ptrBRowSize; // Loop over `B`s rows.
                }

                assembly {
                    mstore(ptrC, c) // Store the result in C[i,j].
                }

                ptrC = ptrC + 32; // Advance to the next element of `C`.
                ptrBCol = ptrBCol + 32; // Advance to the next column of `B`.
            }

            ptrARow = ptrARow + ptrARowSize; // Advance to the next row of `A`.
        }
    }
}

function eq(M32x32 A, M32x32 B) pure returns (bool equals) {
    unchecked {
        if (M32x32.unwrap(A) == M32x32.unwrap(B)) return true;

        (uint256 nA, uint256 mA, uint256 ptrA) = header(A);
        (uint256 nB, uint256 mB, uint256 ptrB) = header(B);

        equals = nA == nB && mA == mB;

        // Loop over `n * m` elements of 8 bytes.
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

                equals := eq(a, b)
            }

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
            uint256 a = (wordA >> ((32 - rest) * 8)) & MAX_64_BITS;
            uint256 b = (wordB >> ((32 - rest) * 8)) & MAX_64_BITS;

            equals = equals && (a == b);
            rest = rest - 8;
        }
    }
}

/* ------------- Mat x scalar operators ------------- */

function addScalarUnchecked(M32x32 A, uint256 s) pure returns (M32x32 C) {
    (uint256 n, uint256 m) = A.shape();

    // Allocate new matrix of the same dimensions.
    C = zerosUnsafe(n, m);

    // Add scalar `s` to `A`, store result in `C`.
    addScalarUncheckedTo_(A, s, C);
}

function addScalarUncheckedTo_(M32x32 A, uint256 s, M32x32 C) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrA) = header(A);

        // Loop over `n * m` elements of 8 bytes.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words.
        uint256 endA = ptrA + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = ptrA + size - endA;
        // Pack `s` in one word for efficiency.
        uint256 valueX4 = packWordUnsafe(s, s, s, s);
        // Obtain a reference to `C`s data location.
        uint256 ptrC = ref(C);

        // Loop over 32 byte words.
        while (ptrA != endA) {
            assembly {
                let a := mload(ptrA) // Load 4 values from `A` at `ptrA`.
                let c := add(a, valueX4) // Add packed values together.

                mstore(ptrC, c) // Store packed `c` in `ptrC`.
            }

            // Advance pointers to next slot.
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

function mulScalarUnchecked(M32x32 A, uint256 s) pure returns (M32x32 C) {
    (uint256 n, uint256 m) = A.shape();

    // Allocate new matrix of the same dimensions.
    C = zerosUnsafe(n, m);

    // Multiply `A` with scalar `s`, store result in `C`.
    mulScalarUncheckedTo_(A, s, C);
}

function mulScalarUncheckedTo_(M32x32 A, uint256 s, M32x32 C) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrA) = header(A);

        // Loop over `n * m` elements of 8 bytes.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words.
        uint256 endA = ptrA + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = ptrA + size - endA;
        // // Pack `s` in one word for efficiency.
        // uint256 valueX4 = packWordUnsafe(s, s, s, s);
        // Obtain a reference to `C`s data location.
        uint256 ptrC = ref(C);

        // Loop over 32 byte words.
        while (ptrA != endA) {
            assembly {
                let a := mload(ptrA) // Load 4 values from `A` at `ptrA`.
                let c := mul(a, s) // Multiply packed values together.

                mstore(ptrC, c) // Store packed `c` in `ptrC`.
            }

            // Advance pointers to next slot.
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

/* ------------- Mat operators ------------- */

function sum(M32x32 A) pure returns (uint256 s) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        // Loop over `n * m` elements of 8 bytes.
        uint256 size = n * m * 8;
        // Up until here we can load & parse full words.
        uint256 end = ptr + (size & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = ptr + size - end;

        // Loop over 32 byte words.
        while (ptr != end) {
            assembly {
                let word := mload(ptr)

                // Add each chunk together.
                s := add(s, and(word, MAX_64_BITS))
                s := add(s, and(shr(64, word), MAX_64_BITS))
                s := add(s, and(shr(128, word), MAX_64_BITS))
                s := add(s, shr(192, word))
            }

            ptr = ptr + 32;
        }

        uint256 word;

        assembly {
            word := mload(ptr)
        }

        // Parse the last remaining word in chunks of 8 bytes.
        while (rest != 0) {
            uint256 a = (word >> ((32 - rest) * 8)) & MAX_64_BITS;

            s = s + a;
            rest = rest - 8;
        }
    }
}

function eqScalar(M32x32 A, uint256 value) pure returns (bool equals) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        // Loop over `n * m` elements of 8 bytes.
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
                let a := mload(ptr)

                equals := eq(a, valueX4)
            }

            if (!equals) break;

            ptr = ptr + 32; // Advance pointer to next slot.
        }

        uint256 word;

        assembly {
            word := mload(ptr)
        }

        // Parse the last remaining word in chunks of 8 bytes.
        while (rest != 0) {
            uint256 a = (word >> ((32 - rest) * 8)) & MAX_64_BITS;

            equals = equals && (a == value);
            rest = rest - 8;
        }
    }
}

function fill_(M32x32 A, uint256 a) pure {
    unchecked {
        (uint256 n, uint256 m, uint256 ptr) = header(A);

        // Loop over `n * m` elements of 8 bytes.
        uint256 end = ptr + ((n * m * 8 + 31) & ~uint256(31));

        // Pack `value` in one word for efficiency.
        uint256 aX4 = packWordUnsafe(a, a, a, a);

        // NOTE: if array is not divisible by 4 we are overshooting.
        while (ptr != end) {
            assembly {
                // Store `a` at current pointer location in all 4 chunks.
                mstore(ptr, aX4)
            }

            ptr = ptr + 32; // Advance pointer to next slot.
        }
    }
}

/* ------------- conversions ------------- */

function from_(bytes memory dataBytes, uint256 n, uint256 m) pure returns (M32x32 A) {
    unchecked {
        if (n * m * 8 > dataBytes.length) revert M32x32_TooLarge();

        uint256 ptr;

        assembly {
            // Actual data is located after length encoding.
            ptr := add(32, dataBytes)
        }

        A = M32x32Header(ptr, n, m);
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

function from(bytes memory dataBytes, uint256 n, uint256 m) view returns (M32x32 A) {
    unchecked {
        if (n * m * 8 > dataBytes.length) revert M32x32_TooLarge();

        uint256 size = n * m * 8;
        uint256 ptr = UM256Lib.malloc(32 + size);

        assembly {
            // Store bytes size.
            mstore(ptr, size)
            // Actual data will be stored in next mem slot.
            ptr := add(ptr, 32)
            // Use `address(4)` precompile to copy memory data `dataBytes` to `ptr`.
            pop(staticcall(gas(), 4, add(32, dataBytes), mload(dataBytes), ptr, size))
        }

        A = M32x32Header(ptr, n, m);
    }
}

function copy(M32x32 A) view returns (M32x32 B) {
    unchecked {
        (uint256 n, uint256 m, uint256 ptrA) = header(A);

        uint256 size = n * m * 8;
        uint256 ptrB = UM256Lib.malloc(32 + size);

        assembly {
            // Store bytes size.
            mstore(ptrB, size)
            // Actual data will be stored in next mem slot.
            ptrB := add(ptrB, 32)
            // Use `address(4)` precompile to copy memory data `ptrA` to `ptrB`.
            pop(staticcall(gas(), 4, ptrA, size, ptrB, size))
        }

        B = M32x32Header(ptrB, n, m);
    }
}

// /* ------------- unsafe conversions ------------- */

// /// @dev `data` needs to be contiguous in memory.
// function fromUnsafe_(uint8[3][4] memory data) pure returns (M32x32 A) {
//     uint256 ptr;

//     assembly {
//         // Making a big assumption here that `data` uint8[3] entries
//         // are laid out contiguously in memory right after the pointers.
//         ptr := mload(data)
//         // Store data bytes length in position `ptr - 32`.
//         // This allows to easily retrieve the underlying data as bytes,
//         // but "destroys" the original `uint8[3][4] memory data` and
//         // it should not be used afterwards.
//         mstore(sub(ptr, 32), 384)
//     }

//     A = M32x32Header(ptr, 4, 3);
// }

// function fromUnsafe_(uint8[3][3] memory data) pure returns (M32x32 A) {
//     uint256 ptr;

//     assembly {
//         ptr := mload(data)
//     }

//     A = M32x32Header(ptr, 3, 3);
// }

function packWordUnsafe(uint256 a, uint256 b, uint256 c, uint256 d) pure returns (uint256 word) {
    word = (a << 192) | (b << 128) | (c << 64) | d;
}
