// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import { M32x32 } from "src/M32x32.sol";
import { N32x32, ONE, HALF } from "src/N32x32.sol";
import { Random, seed } from "src/Random.sol";
import { TestHelper } from "./utils/TestHelper.sol";

// contract TestRandom is TestHelper {
//     /* ------------- constructors ------------- */

//     function test_rand() public {
//         Random r = seed(0);

//         M32x32 R = r.rand(2, 4);

//         logMat(R, 8);

//         assertLt(R, 1 << 32);
//         assertGt(R, 0);

//         logNum("mean", N32x32.wrap(int64(uint64(R.mean()))));
//         // console.log("mean", R.mean());
//     }

//     function test_rand_mean() public {
//         Random r = seed(123);

//         M32x32 R = r.rand(1, 200);
//         logMat(R);

//         // logNum(R.mean());
//         // assertApproxEqAbs(N32x32.wrap(int64(uint64(R.mean()))), 0.1 ether);
//         // assertApproxEqAbs(R.mean(), HALF, ONE.div(10));
//     }

//     function test_randn() public {
//         Random r = seed(0);

//         // M32x32 R = r.randn(4, 4);

//         // logMat(R, 8);
//         // logNum("mean", N32x32.wrap(int64(int64(R.mean()))));

//         // assertLt(R, 1 << 32);
//         // assertGt(R, 0);

//         // logNum(N32x32.wrap(int64(uint64(R.mean()))));
//         // console.log("mean", R.mean());
//     }

//     // // note: does not handle overflow.
//     // function test_packed_arithmetic(
//     //     uint32 a1,
//     //     uint32 a2,
//     //     uint32 a3,
//     //     uint32 a4,
//     //     uint32 b1,
//     //     uint32 b2,
//     //     uint32 b3,
//     //     uint32 b4
//     // ) public {
//     //     a1 = uint32(int32(bound(int256(int32(a1)), int256(type(int16).min), int256(type(int16).max))));
//     //     a2 = uint32(int32(bound(int256(int32(a2)), int256(type(int16).min), int256(type(int16).max))));
//     //     a3 = uint32(int32(bound(int256(int32(a3)), int256(type(int16).min), int256(type(int16).max))));
//     //     a4 = uint32(int32(bound(int256(int32(a4)), int256(type(int16).min), int256(type(int16).max))));

//     //     b1 = uint32(int32(bound(int256(int32(b1)), int256(type(int16).min), int256(type(int16).max))));
//     //     b2 = uint32(int32(bound(int256(int32(b2)), int256(type(int16).min), int256(type(int16).max))));
//     //     b3 = uint32(int32(bound(int256(int32(b3)), int256(type(int16).min), int256(type(int16).max))));
//     //     b4 = uint32(int32(bound(int256(int32(b4)), int256(type(int16).min), int256(type(int16).max))));

//     //     uint256 aX4 = (a1 << 192) | (a2 << 128) | (a3 << 64) | a4;
//     //     uint256 bX4 = (b1 << 192) | (b2 << 128) | (b3 << 64) | b4;

//     //     int32 c1 = int32(a1) - int32(b1);
//     //     int32 c2 = int32(a2) - int32(b2);
//     //     int32 c3 = int32(a3) - int32(b3);
//     //     int32 c4 = int32(a4) - int32(b4);

//     //     uint256 cX4 = (uint256(uint32(c1)) << 192) | (uint256(uint32(c2)) << 128) | (uint256(uint32(c3)) << 64)
//     //         | uint256(uint32(c4));

//     //     unchecked {
//     //         console.logBytes32(bytes32(aX4 - bX4));
//     //         assertEq(aX4 - bX4, cX4);
//     //     }
//     // }
// }

// contract TestGasRandom {
//     function test_perf_rand_128() public pure {
//         Random r = seed(0);

//         r.rand(128, 128);
//     }
// }
