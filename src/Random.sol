// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "./UM256.sol" as UM256Lib;
import "./M32x32.sol" as M32x32Lib;

import { UM256, mallocUM256 } from "./UM256.sol";
import { M32x32, mallocM32x32, UINT32_MAX } from "./M32x32.sol";
import { UINT64_MAX, N32x32 } from "./N32x32.sol";

type Random is uint256;

using { randUint, randInt, getSeed, setSeed, rand, randn, addRandn, addRandnTo_, randUM256 } for Random global;

function seed(uint256 randomSeed) pure returns (Random r) {
    assembly {
        r := mload(0x40)
        mstore(0x40, add(32, r))
        mstore(r, randomSeed)
    }
}

function setSeed(Random r, uint256 randomSeed) pure {
    assembly {
        mstore(r, randomSeed)
    }
}

function getSeed(Random r) pure returns (uint256 randomSeed) {
    assembly {
        randomSeed := mload(r)
    }
}

function randUint(Random r) pure returns (uint256 value) {
    assembly {
        value := keccak256(r, 32)
        mstore(r, value)
    }
}

function randInt(Random r) pure returns (int256 value) {
    assembly {
        value := keccak256(r, 32)
        mstore(r, value)
    }
}

function randUM256(Random r, uint256 n, uint256 m) pure returns (UM256 A) {
    unchecked {
        // Allocate memory for matrix.
        A = mallocUM256(n, m);

        // Obtain a pointer to matrix data location.
        uint256 ptr = A.ref();

        // Loop over n * m elements of 32 bytes.
        uint256 end = ptr + n * m * 32;

        // Update random seed when iterating over elements.
        uint256 randomSeed;

        while (ptr != end) {
            assembly {
                randomSeed := keccak256(r, 32) // Generate a new random number.
                mstore(ptr, randomSeed) // Store `a` at current pointer location.
            }

            ptr = ptr + 32; // Advance pointer to the next slot.
        }

        assembly {
            // Store the updated random seed in `r`.
            mstore(r, randomSeed)
        }
    }
}

uint256 constant UINT8_MAX_X16 = 0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff;
uint256 constant UINT16_MAX_X8 = 0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff;
uint256 constant UINT32_MAX_X4 = 0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff;
uint256 constant HALF_M32x32_X4 = 0x0000000080000000000000008000000000000000800000000000000080000000;
uint256 constant ONES_X4 = 0x0000000000000001000000000000000100000000000000010000000000000001;
uint256 constant ONES_X16 = 0x0001000100010001000100010001000100010001000100010001000100010001;

function rand(Random r, uint256 n, uint256 m) pure returns (M32x32 A) {
    unchecked {
        // Allocate memory for matrix.
        A = mallocM32x32(n, m);

        // Loop over all `n * m` elements of 8 bytes.
        uint256 size = n * m * 8;
        // Obtain a pointer to matrix data location.
        uint256 ptr = A.ref();
        // Up until here we can parse two full words (8 elements).
        uint256 end = ptr + ((size + 63) & ~uint256(63));
        // uint256 end = ptr + ((size + 31) & ~uint256(31));
        // The rest needs to be parsed individually.
        uint256 rest = size & 63;

        // Update random seed when iterating over elements.
        uint256 randomSeed;

        while (ptr != end) {
            assembly {
                randomSeed := keccak256(r, 32) // Generate a new random number.
                mstore(r, randomSeed) // Store the updated random seed in `r`.

                let aX4 := shr(32, and(randomSeed, not(UINT32_MAX_X4))) // Apply mask to fractional part.
                mstore(ptr, aX4) // Store packed `a` at current pointer location.
                ptr := add(ptr, 32) // Advance pointer to the next slot.

                aX4 := and(randomSeed, UINT32_MAX_X4) // Apply mask to fractional part.
                mstore(ptr, aX4) // Store packed `a` at current pointer location.
                ptr := add(ptr, 32) // Advance pointer to the next slot.
            }
        }

        if (rest != 0) {
            assembly {
                randomSeed := keccak256(r, 32) // Generate a new random number.
                mstore(r, randomSeed) // Store the updated random seed in `r`.
            }

            uint256 aX4;

            if (rest >= 32) {
                assembly {
                    aX4 := shr(32, and(randomSeed, shl(32, UINT32_MAX_X4))) // Apply mask to fractional part.
                    mstore(ptr, aX4) // Store packed `a` at current pointer location.
                    ptr := add(ptr, 32) // Advance pointer to the next slot.
                }

                rest = rest - 32;
            }

            assembly {
                // let mask := not(shr(mul(rest, 8), not(0))) // Mask applies to leftover bits in word.
                aX4 := and(randomSeed, UINT32_MAX_X4) // Apply mask to fractional part.
                mstore(ptr, aX4) // Store packed `a` at current pointer location.
            }
        }
    }
}

/// We use the central limit theorem for sampling from
/// the normal distribution, given a uniform sampling method.
///
/// 𝑁(0,1) ≈ √𝑛(𝑆𝑛−𝜇)/𝜎
///
/// Sn = ∑Xi , where Xi is uniformly sampled.
///
/// We sample 8 numbers from the interval [0, 1].
/// Then √𝑛 = 4, 𝜎 = √12
function randn(Random r, uint256 n, uint256 m) pure returns (M32x32 A) {
    unchecked {
        // Allocate memory for matrix.
        A = mallocM32x32(n, m);

        // Obtain a pointer to matrix data location.
        uint256 ptr = A.ref();

        // Loop over all `n * m` elements of 8 bytes.
        uint256 end = ptr + ((n * m * 8 + 31) & ~uint256(31));

        // Update random seed when iterating over elements.
        uint256 randomSeed;

        while (ptr != end) {
            assembly {
                let rn, rX4

                randomSeed := keccak256(r, 32) // Generate a new random number.
                mstore(r, randomSeed) // Store the updated random seed in `r`.

                // Sample a random normal variable.
                rn := and(randomSeed, UINT32_MAX_X4) // Add masked halves together.
                rn := add(rn, shr(32, and(randomSeed, not(UINT32_MAX_X4))))
                rn := mul(rn, ONES_X4) // Multiply by `1 + (1 << 64) + (1 << 128) + (1 << 192)`.
                rn := shr(192, rn) // The sum is located at bit pos 192.
                rn := sub(rn, 0x400000000) // Center (subtract N times mean = `8 * 0x80000000`).
                rn := mul(rn, 42081913348) // Multiply by `sqrt(N / variance) = sqrt(8 * 12) << 32`.
                rn := shr(35, rn) // Shift back by 32 bits. Take average: Divide by `N = 8`.

                rX4 := and(rn, UINT64_MAX)

                randomSeed := keccak256(r, 32) // Generate a new random number.
                mstore(r, randomSeed) // Store the updated random seed in `r`.

                // Sample a random normal variable.
                rn := add(and(randomSeed, UINT32_MAX_X4), shr(32, and(randomSeed, not(UINT32_MAX_X4))))
                rn := shr(35, mul(sub(shr(192, mul(rn, ONES_X4)), 0x400000000), 42081913348))

                rX4 := or(rX4, shl(64, and(rn, UINT64_MAX)))

                randomSeed := keccak256(r, 32) // Generate a new random number.
                mstore(r, randomSeed) // Store the updated random seed in `r`.

                // Sample a random normal variable.
                rn := add(and(randomSeed, UINT32_MAX_X4), shr(32, and(randomSeed, not(UINT32_MAX_X4))))
                rn := shr(35, mul(sub(shr(192, mul(rn, ONES_X4)), 0x400000000), 42081913348))

                rX4 := or(rX4, shl(128, and(rn, UINT64_MAX)))

                randomSeed := keccak256(r, 32) // Generate a new random number.
                mstore(r, randomSeed) // Store the updated random seed in `r`.

                // Sample a random normal variable.
                rn := add(and(randomSeed, UINT32_MAX_X4), shr(32, and(randomSeed, not(UINT32_MAX_X4))))
                rn := shr(35, mul(sub(shr(192, mul(rn, ONES_X4)), 0x400000000), 42081913348))

                rX4 := or(rX4, shl(192, rn))

                randomSeed := keccak256(r, 32) // Generate a new random number.
                mstore(r, randomSeed) // Store the updated random seed in `r`.

                mstore(ptr, rX4)
            }

            ptr = ptr + 32;
        }
    }
}

function addRandn(Random r, M32x32 A, N32x32 scale) view returns (M32x32 C) {
    C = A.copy();

    addRandnTo_(r, C, scale);
}

function addRandnTo_(Random r, M32x32 A, N32x32 scale) pure {
    unchecked {
        uint256 n;
        uint256 m;
        uint256 ptr;

        // Obtain a pointer to matrix data location.
        (n, m, ptr) = A.header();

        // Loop over all `n * m` elements of 8 bytes.
        uint256 end = ptr + ((n * m * 8 + 31) & ~uint256(31));

        // Update random seed when iterating over elements.
        uint256 randomSeed;

        // Pre-compute multiplier.
        uint256 multiplier;
        assembly {
            multiplier := mul(scale, 42081913348) // Multiply scale by `sqrt(N / variance) = sqrt(8 * 12) << 32`.
        }

        while (ptr != end) {
            assembly {
                let rn, rX4

                let aX4 := mload(ptr)

                randomSeed := keccak256(r, 32) // Generate a new random number.
                mstore(r, randomSeed) // Store the updated random seed in `r`.

                // Sample a random normal variable.
                rn := and(randomSeed, UINT32_MAX_X4) // Add masked halves together.
                rn := add(rn, shr(32, and(randomSeed, not(UINT32_MAX_X4))))
                rn := mul(rn, ONES_X4) // Multiply by `1 + (1 << 64) + (1 << 128) + (1 << 192)`.
                rn := shr(192, rn) // The sum is located at bit pos 192.
                rn := sub(rn, 0x400000000) // Center (subtract N times mean = `8 * 0x80000000`).
                rn := mul(rn, multiplier) // Multiply by `scale * sqrt(N / variance) = scale * sqrt(8 * 12) << 32`.
                rn := sar(67, rn) // Shift back by 64 bits. Take average: Divide by `N = 8`.

                rX4 := and(rn, UINT64_MAX)

                randomSeed := keccak256(r, 32) // Generate a new random number.
                mstore(r, randomSeed) // Store the updated random seed in `r`.

                // Sample a random normal variable.
                rn := add(and(randomSeed, UINT32_MAX_X4), shr(32, and(randomSeed, not(UINT32_MAX_X4))))
                rn := sar(67, mul(sub(shr(192, mul(rn, ONES_X4)), 0x400000000), multiplier))

                rX4 := or(rX4, shl(64, and(rn, UINT64_MAX)))

                randomSeed := keccak256(r, 32) // Generate a new random number.
                mstore(r, randomSeed) // Store the updated random seed in `r`.

                // Sample a random normal variable.
                rn := add(and(randomSeed, UINT32_MAX_X4), shr(32, and(randomSeed, not(UINT32_MAX_X4))))
                rn := sar(67, mul(sub(shr(192, mul(rn, ONES_X4)), 0x400000000), multiplier))

                rX4 := or(rX4, shl(128, and(rn, UINT64_MAX)))

                randomSeed := keccak256(r, 32) // Generate a new random number.
                mstore(r, randomSeed) // Store the updated random seed in `r`.

                // Sample a random normal variable.
                rn := add(and(randomSeed, UINT32_MAX_X4), shr(32, and(randomSeed, not(UINT32_MAX_X4))))
                rn := sar(67, mul(sub(shr(192, mul(rn, ONES_X4)), 0x400000000), multiplier))

                rX4 := or(rX4, shl(192, rn))

                randomSeed := keccak256(r, 32) // Generate a new random number.
                mstore(r, randomSeed) // Store the updated random seed in `r`.

                mstore(ptr, rX4)
            }

            ptr = ptr + 32;
        }
    }
}

// function randn2(Random r, uint256 n, uint256 m) pure returns (M32x32 A) {
//     unchecked {
//         // Allocate memory for matrix.
//         A = mallocM32x32(n, m);

//         // Obtain a pointer to matrix data location.
//         uint256 ptr = A.ref();

//         // Loop over all `n * m` elements of 8 bytes.
//         uint256 end = ptr + ((n * m * 8 + 31) & ~uint256(31));

//         // Update random seed when iterating over elements.
//         uint256 randomSeed;

//         while (ptr != end) {
//             assembly {
//                 let rn, rX4

//                 randomSeed := keccak256(r, 32) // Generate a new random number.
//                 mstore(r, randomSeed) // Store the updated random seed in `r`.

//                 // Sample a random normal variable.
//                 rn := and(randomSeed, UINT8_MAX_X16) // Add masked halves together.
//                 rn := add(rn, shr(8, and(randomSeed, not(UINT8_MAX_X16))))
//                 rn := mul(rn, ONES_X16) // Multiply by ones...
//                 rn := shr(253, rn) // The sum is located at bit pos 248 (= 256 - 8). Take average: divide by `N = 32` (5 shifts).
//                 rn := sub(rn, 0x80000000) // Center (subtract mean).
//                 rn := shr(32, mul(rn, 84163826697)) // Multiply by `sqrt(N / variance) = sqrt(32 * 12) << 32`.

//                 rX4 := and(rn, UINT64_MAX)

//                 randomSeed := keccak256(r, 32) // Generate a new random number.
//                 mstore(r, randomSeed) // Store the updated random seed in `r`.

//                 // Sample a random normal variable.
//                 rn := add(and(randomSeed, UINT8_MAX_X16), shr(8, and(randomSeed, not(UINT8_MAX_X16))))
//                 rn := shr(32, mul(sub(shr(253, mul(rn, ONES_X16)), 0x80000000), 84163826697))

//                 rX4 := or(rX4, shl(64, and(rn, UINT64_MAX)))

//                 randomSeed := keccak256(r, 32) // Generate a new random number.
//                 mstore(r, randomSeed) // Store the updated random seed in `r`.

//                 // Sample a random normal variable.
//                 rn := add(and(randomSeed, UINT8_MAX_X16), shr(8, and(randomSeed, not(UINT8_MAX_X16))))
//                 rn := shr(32, mul(sub(shr(253, mul(rn, ONES_X16)), 0x80000000), 84163826697))

//                 rX4 := or(rX4, shl(128, and(rn, UINT64_MAX)))

//                 randomSeed := keccak256(r, 32) // Generate a new random number.
//                 mstore(r, randomSeed) // Store the updated random seed in `r`.

//                 // Sample a random normal variable.
//                 rn := add(and(randomSeed, UINT8_MAX_X16), shr(8, and(randomSeed, not(UINT8_MAX_X16))))
//                 rn := shr(32, mul(sub(shr(253, mul(rn, ONES_X16)), 0x80000000), 84163826697))

//                 rX4 := or(rX4, shl(192, rn))

//                 randomSeed := keccak256(r, 32) // Generate a new random number.
//                 mstore(r, randomSeed) // Store the updated random seed in `r`.

//                 mstore(ptr, rX4)
//             }

//             ptr = ptr + 32;
//         }
//     }
// }

// library Random {
//     bytes32 constant RANDOM_SEED_SLOT = 0x6e377520b7c8a184bde346d33005e4a5bae120b4ba0ebf9af2278ce0bb899ee1;

//     function seed(uint256 randomSeed) internal {
//         assembly {
//             sstore(RANDOM_SEED_SLOT, randomSeed)
//         }
//     }

//     function seed() internal view returns (uint256 randomSeed) {
//         assembly {
//             randomSeed := sload(RANDOM_SEED_SLOT)
//         }
//     }

//     function next() internal returns (uint256) {
//         return next(0, type(uint256).max);
//     }

//     function nextAddress() internal returns (address) {
//         return address(uint160(next(0, type(uint256).max)));
//     }

//     function next(uint256 high) internal returns (uint256) {
//         return next(0, high);
//     }

//     function next(uint256 low, uint256 high) internal returns (uint256 nextRandom) {}

//     function next(uint256 low, uint256 high) internal returns (uint256 nextRandom) {
//         uint256 randomSeed;

//         assembly {
//             randomSeed := sload(RANDOM_SEED_SLOT)
//         }

//         // make sure this was intentionally set to 0
//         // otherwise fuzz-runs could have an uninitialized seed
//         if (randomSeed == 0) {
//             bool randomSeedSet;

//             require(randomSeedSet, "Random seed unset.");
//         }

//         return nextFromRandomSeed(low, high, randomSeed);
//     }

//     function nextFromRandomSeed(uint256 low, uint256 high, uint256 randomSeed) internal returns (uint256 nextRandom)
// {
//         require(low <= high, "low > high");

//         assembly {
//             mstore(0, randomSeed)
//             nextRandom := keccak256(0, 0x20)
//             sstore(RANDOM_SEED_SLOT, nextRandom)
//         }

//         nextRandom = low + (nextRandom % (high - low));
//     }

//     function randUint(uint256 low, uint256 high, uint256 randomSeed) internal returns (uint256 nextRandom) {
//         unchecked {
//             nextRandom = low + (randUint(randomSeed) % (high - low));
//         }
//     }

//     function randUint(uint256 randomSeed) internal returns (uint256 nextRandom) {
//         assembly {
//             mstore(0, randomSeed)
//             nextRandom := keccak256(0, 0x20)
//             sstore(RANDOM_SEED_SLOT, nextRandom)
//         }
//     }
// }
