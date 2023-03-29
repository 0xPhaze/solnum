// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "./UM256.sol" as UM256Lib;
import "./M32x32.sol" as M32x32Lib;

import {UM256, mallocUM256} from "./UM256.sol";
import {M32x32, mallocM32x32, UINT32_MASK} from "./M32x32.sol";

type Random is uint256;

using {next, getSeed, rand, randn, randUM256} for Random global;

function seed(uint256 randomSeed) pure returns (Random r) {
    assembly {
        r := mload(0x40)
        mstore(0x40, add(32, r))
        mstore(r, randomSeed)
    }
}

function getSeed(Random r) pure returns (uint256 randomSeed) {
    assembly {
        randomSeed := mload(r)
    }
}

function next(Random r) pure returns (uint256 value) {
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

uint256 constant MASK_M32x32_FRACTIONS_X4 = 0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff;
uint256 constant HALF_M32x32_X4 = 0x0000000080000000000000008000000000000000800000000000000080000000;

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

                let aX4 := shr(32, and(randomSeed, shl(32, MASK_M32x32_FRACTIONS_X4))) // Apply mask to fractional part.
                mstore(ptr, aX4) // Store packed `a` at current pointer location.
                ptr := add(ptr, 32) // Advance pointer to the next slot.

                aX4 := and(randomSeed, MASK_M32x32_FRACTIONS_X4) // Apply mask to fractional part.
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
                    aX4 := shr(32, and(randomSeed, shl(32, MASK_M32x32_FRACTIONS_X4))) // Apply mask to fractional part.
                    mstore(ptr, aX4) // Store packed `a` at current pointer location.
                    ptr := add(ptr, 32) // Advance pointer to the next slot.
                }

                rest = rest - 32;
            }

            assembly {
                // let mask := not(shr(mul(rest, 8), not(0))) // Mask applies to leftover bits in word.
                aX4 := and(randomSeed, MASK_M32x32_FRACTIONS_X4) // Apply mask to fractional part.
                mstore(ptr, aX4) // Store packed `a` at current pointer location.
            }
        }
    }
}

uint256 constant RANDN_MAX_ITER = 2;

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
            // uint256 s;
            // uint256 aX4;
            // uint256 iter;

            // while (iter < RANDN_MAX_ITER) {
            uint256 r1;
            uint256 r2;
            uint256 r3;
            uint256 r4;
            assembly {
                randomSeed := keccak256(r, 32) // Generate a new random number.
                mstore(r, randomSeed) // Store the updated random seed in `r`.

                // Sum all 8 fractional random numbers together
                r1 := and(randomSeed, UINT32_MASK)
                randomSeed := shr(32, randomSeed)
                r1 := add(r1, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r1 := add(r1, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r1 := add(r1, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r1 := add(r1, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r1 := add(r1, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r1 := add(r1, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r1 := add(r1, randomSeed)
                r1 := div(sub(r1, shl(4, 32)), 8)

                randomSeed := keccak256(r, 32) // Generate a new random number.
                mstore(r, randomSeed) // Store the updated random seed in `r`.

                r2 := and(randomSeed, UINT32_MASK)
                randomSeed := shr(32, randomSeed)
                r2 := add(r2, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r2 := add(r2, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r2 := add(r2, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r2 := add(r2, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r2 := add(r2, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r2 := add(r2, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r2 := add(r2, randomSeed)
                r2 := div(sub(r2, shl(4, 32)), 8)

                randomSeed := keccak256(r, 32) // Generate a new random number.
                mstore(r, randomSeed) // Store the updated random seed in `r`.

                r3 := and(randomSeed, UINT32_MASK)
                randomSeed := shr(32, randomSeed)
                r3 := add(r3, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r3 := add(r3, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r3 := add(r3, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r3 := add(r3, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r3 := add(r3, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r3 := add(r3, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r3 := add(r3, randomSeed)
                r3 := div(sub(r3, shl(4, 32)), 8)

                randomSeed := keccak256(r, 32) // Generate a new random number.
                mstore(r, randomSeed) // Store the updated random seed in `r`.

                r4 := and(randomSeed, UINT32_MASK)
                randomSeed := shr(32, randomSeed)
                r4 := add(r4, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r4 := add(r4, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r4 := add(r4, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r4 := add(r4, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r4 := add(r4, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r4 := add(r4, and(randomSeed, UINT32_MASK))
                randomSeed := shr(32, randomSeed)
                r4 := add(r4, randomSeed)
                r4 := div(sub(r4, shl(4, 32)), 8)
            }

            uint256 rX4 = M32x32Lib.packWordUnsafe(r1, r2, r3, r4);

            assembly {
                mstore(ptr, rX4)
            }

            ptr = ptr + 32;
        }
    }
}

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

//     function nextFromRandomSeed(uint256 low, uint256 high, uint256 randomSeed) internal returns (uint256 nextRandom) {
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
