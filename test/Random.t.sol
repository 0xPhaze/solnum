// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import { M32x32 } from "src/M32x32.sol";
// import { N32x32, ZERO, ONE, HALF } from "src/N32x32.sol";
// import { Random, seed } from "src/Random.sol";
import "src/N32x32.sol";
import "src/Random.sol";
import { TestHelper, console } from "./utils/TestHelper.sol";

contract TestRandom is TestHelper {
    /* ------------- constructors ------------- */

    function test_rand(uint256 n, uint256 m, uint256 s) public {
        n = bound(n, 1, 10);
        m = bound(m, 1, 10);

        Random r = seed(s);
        M32x32 R = r.rand(n, m);

        assertLt(R, ONE);
        assertGt(R, ZERO);

        // logNum("mean", N32x32.wrap(int64(uint64(R.mean()))));
        // logNum("mean", R.mean());
    }

    function test_rand_mean() public {
        Random r = seed(0);

        M32x32 R = r.rand(1, 10_000);

        assertApproxEqAbs(R.mean(), HALF, ONE.divInt(1_000));
        assertApproxEqAbs(R.vari(), ONE.divInt(12), ONE.divInt(1_000));
    }

    function test_randn() public {
        Random r = seed(0);
        M32x32 R = r.randn(1, 10_000);

        logNum("min", R.min());
        logNum("max", R.max());

        // assertLt(R.abs(), ONE.mulInt(10));
        // assertGt(R, ZERO);

        assertApproxEqAbs(R.mean(), ZERO, ONE.divInt(100));
        assertApproxEqAbs(R.vari(), ONE, ONE.divInt(100));
    }

    function test_xxx(uint256 randomSeed) public {
        // function test_xxx() public {
        // Random r = seed(0);
        // uint256 randomSeed = r.randUint();

        int256 r1;
        assembly {
            // Sample a random normal variable.
            r1 := and(randomSeed, UINT32_MAX_X4) // Add masked halves together.
            r1 := add(r1, shr(32, and(randomSeed, not(UINT32_MAX_X4))))
            r1 := mul(r1, ONES_X4) // Multiply by `1 + (1 << 64) + (1 << 128) + (1 << 192)`.
            // r1 := sar(222, r1)
            r1 := shr(190, r1)
            // r1 := mul(4, r1) // The sum is located at bit pos 192. Multiply by `sqrt(N) = 4`.
            r1 := sub(r1, shl(32, 4)) // Subtract `8 * mean = 4 << 32`.
            r1 := sdiv(r1, 14878203147) // Divide by `sqrt(12) << 32`.
        }

        // Summing 8 packed uint64s.
        int256 sum1;

        unchecked {
            for (uint256 i; i < 8; i++) {
                // sum1 += int32(uint32(randomSeed >> i * 32));
                sum1 += int256(uint256(uint32(randomSeed >> i * 32)));
                // sum1 += int256(int64(uint64(randomSeed >> i * 32)));
            }
        }

        unchecked {
            sum1 = sum1 * 4 - (4 << 32);
            sum1 = sum1 / 14878203147;
        }

        assertEq(r1, sum1);
    }

    // // note: does not handle overflow.
    // function test_packed_arithmetic(
    //     uint32 a1,
    //     uint32 a2,
    //     uint32 a3,
    //     uint32 a4,
    //     uint32 b1,
    //     uint32 b2,
    //     uint32 b3,
    //     uint32 b4
    // ) public {
    //     a1 = uint32(int32(bound(int256(int32(a1)), int256(type(int16).min), int256(type(int16).max))));
    //     a2 = uint32(int32(bound(int256(int32(a2)), int256(type(int16).min), int256(type(int16).max))));
    //     a3 = uint32(int32(bound(int256(int32(a3)), int256(type(int16).min), int256(type(int16).max))));
    //     a4 = uint32(int32(bound(int256(int32(a4)), int256(type(int16).min), int256(type(int16).max))));

    //     b1 = uint32(int32(bound(int256(int32(b1)), int256(type(int16).min), int256(type(int16).max))));
    //     b2 = uint32(int32(bound(int256(int32(b2)), int256(type(int16).min), int256(type(int16).max))));
    //     b3 = uint32(int32(bound(int256(int32(b3)), int256(type(int16).min), int256(type(int16).max))));
    //     b4 = uint32(int32(bound(int256(int32(b4)), int256(type(int16).min), int256(type(int16).max))));

    //     uint256 aX4 = (a1 << 192) | (a2 << 128) | (a3 << 64) | a4;
    //     uint256 bX4 = (b1 << 192) | (b2 << 128) | (b3 << 64) | b4;

    //     int32 c1 = int32(a1) - int32(b1);
    //     int32 c2 = int32(a2) - int32(b2);
    //     int32 c3 = int32(a3) - int32(b3);
    //     int32 c4 = int32(a4) - int32(b4);

    //     uint256 cX4 = (uint256(uint32(c1)) << 192) | (uint256(uint32(c2)) << 128) | (uint256(uint32(c3)) << 64)
    //         | uint256(uint32(c4));

    //     unchecked {
    //         console.logBytes32(bytes32(aX4 - bX4));
    //         assertEq(aX4 - bX4, cX4);
    //     }
    // }
}

// contract TestGasRandom {
//     function test_perf_rand_128() public pure {
//         Random r = seed(0);

//         r.rand(128, 128);
//     }
// }
