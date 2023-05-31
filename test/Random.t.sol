// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import { M32x32, M32x32Lib } from "../src/M32x32.sol";
// import "src/M32x32.sol" as sn;
// import "src/M32x32.sol";
// import { N32x32, N32x32Lib.ZERO, N32x32Lib.ONE, N32x32Lib.HALF } from "../src/N32x32.sol";
// import { Random, RandomLib.seed } from "../src/Random.sol";
import { N32x32, N32x32Lib } from "../src/N32x32.sol";
import { Random, RandomLib } from "../src/Random.sol";
import { SolnumTestHelper, console } from "../src/utils/SolnumTestHelper.sol";

contract TestRandom is SolnumTestHelper {
    /* ------------- constructors ------------- */

    function test_rand(uint256 n, uint256 m, uint256 s) public {
        n = bound(n, 1, 10);
        m = bound(m, 1, 10);

        Random r;
        r.setSeed(s);
        M32x32 R = r.rand(n, m);

        assertLt(R, N32x32Lib.ONE);
        assertGt(R, N32x32Lib.ZERO);

        // logNum("mean", N32x32.wrap(int64(uint64(R.mean()))));
        // logNum("mean", R.mean());
    }

    function test_rand_mean() public {
        Random r = RandomLib.seed(0);

        M32x32 R = r.rand(1, 10_000);

        assertApproxEqAbs(R.mean(), N32x32Lib.HALF, N32x32Lib.ONE.divInt(1_000));
        assertApproxEqAbs(R.vari(), N32x32Lib.ONE.divInt(12), N32x32Lib.ONE.divInt(1_000));
    }

    function test_randn() public {
        Random r = RandomLib.seed(0);
        M32x32 R = r.randn(1, 10_000);

        // logNum("min", R.min());
        // logNum("max", R.max());

        assertApproxEqAbs(R.mean(), N32x32Lib.ZERO, N32x32Lib.ONE.divInt(100));
        assertApproxEqAbs(R.vari(), N32x32Lib.ONE, N32x32Lib.ONE.divInt(100));
    }

    function test_addRandn() public {
        Random r = RandomLib.seed(0);
        M32x32 R = r.randn(1, 100);

        r.setSeed(0);
        M32x32 R2 = r.addRandn(M32x32Lib.zeros(1, 100), N32x32Lib.ONE);

        assertEq(R, R2);

        r.setSeed(0);
        R2 = r.addRandn(M32x32Lib.zeros(1, 100), N32x32Lib.NEG_ONE).mulInt(-1).addScalar(N32x32.wrap(-1));

        assertEq(R, R2);

        r.setSeed(0);
        N32x32 bias = N32x32.wrap(0x1234fffffffff);
        R2 = r.addRandn(M32x32Lib.full(1, 100, bias), N32x32Lib.ONE.mulInt(1337)).addScalar(bias.mulInt(-1));

        assertApproxEqAbs(R.max(), R2.max().divInt(1337), N32x32Lib.ONE.divInt(1_000_000));
        assertApproxEqAbs(R.min(), R2.min().divInt(1337), N32x32Lib.ONE.divInt(1_000_000));
    }

    function test_addRandn_revert_Overflow() public {
        Random r = RandomLib.seed(0);
        vm.expectRevert(N32x32Lib.Overflow.selector);

        r.addRandn(M32x32Lib.full(1, 100, N32x32Lib.MAX.sub(N32x32Lib.ONE)), N32x32Lib.ONE);
    }

    function test_addRandnToWithDecay() public {
        Random r = RandomLib.seed(0);
        M32x32 R1 = r.addRandn(M32x32Lib.ones(1, 100), N32x32Lib.ONE);

        r.setSeed(0);
        M32x32 R2 = M32x32Lib.ones(1, 100);
        r.addRandnToWithDecay_(R2, N32x32Lib.ONE, N32x32Lib.ONE, R2);

        assertEq(R1, R2);
    }

    function test_moons_learn() public {
        M32x32 X = M32x32Lib.fromIntEncoded(
            hex"000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000000000000000000000000000000000000000000000000000000000000002fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000000000000000000000000000000002fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000dfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000009000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000008fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd0000000000000000000000000000000000000000000000000000000000000009000000000000000000000000000000000000000000000000000000000000000afffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000120000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000bfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000bfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb00000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000006fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd0000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000012ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff700000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000005fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000008fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000500000000000000000000000000000000000000000000000000000000000000140000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb00000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff600000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000011fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000b00000000000000000000000000000000000000000000000000000000000000140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000003fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000004fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000008fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff70000000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb00000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000140000000000000000000000000000000000000000000000000000000000000002fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000000000000000000000000000900000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000009000000000000000000000000000000000000000000000000000000000000000efffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000002fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000008fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9000000000000000000000000000000000000000000000000000000000000000600000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000005000000000000000000000000000000000000000000000000000000000000000cfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd000000000000000000000000000000000000000000000000000000000000000900000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000003fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000013000000000000000000000000000000000000000000000000000000000000000500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050000000000000000000000000000000000000000000000000000000000000006fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff500000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000006fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd0000000000000000000000000000000000000000000000000000000000000002ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000150000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000cfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000130000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000130000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd0000000000000000000000000000000000000000000000000000000000000010fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90000000000000000000000000000000000000000000000000000000000000005fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000009000000000000000000000000000000000000000000000000000000000000000b0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000010ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000001100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000010fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000000000000000000000000000efffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000090000000000000000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000008fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb000000000000000000000000000000000000000000000000000000000000000500000000000000000000000000000000000000000000000000000000000000070000000000000000000000000000000000000000000000000000000000000012000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004"
        ).reshape(100, 2);
        M32x32 Y = M32x32Lib.fromIntEncoded(
            hex"0000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001"
        ).reshape(100, 1);

        M32x32[] memory A = new M32x32[](3);
        M32x32[] memory b = new M32x32[](3);

        A[0] = M32x32Lib.zeros(16, 2);
        b[0] = M32x32Lib.zeros(1, 16);
        A[1] = M32x32Lib.zeros(16, 16);
        b[1] = M32x32Lib.zeros(1, 16);
        A[2] = M32x32Lib.zeros(1, 16);
        b[2] = M32x32Lib.zeros(1, 1);

        // console.log(b[0].sizeBytes() & 31);

        N32x32 g = N32x32Lib.ONE.divInt(100);
        N32x32 d = N32x32Lib.ONE.mulInt(10).divInt(10);

        M32x32[] memory A_ = new M32x32[](3);
        M32x32[] memory b_ = new M32x32[](3);

        A_[0] = M32x32Lib.mallocLike(A[0]);
        b_[0] = M32x32Lib.mallocLike(b[0]);
        A_[1] = M32x32Lib.mallocLike(A[1]);
        b_[1] = M32x32Lib.mallocLike(b[1]);
        A_[2] = M32x32Lib.mallocLike(A[2]);
        b_[2] = M32x32Lib.mallocLike(b[2]);

        N32x32 bestScore;

        Random r = RandomLib.seed(0);
        // logMat('X', X);
        // logMat('Y', Y);

        for (uint256 i; i < 1000; i++) {
            r.addRandnToWithDecay_(A[0], g, d, A_[0]);
            r.addRandnToWithDecay_(b[0], g, d, b_[0]);

            r.addRandnToWithDecay_(A[1], g, d, A_[1]);
            r.addRandnToWithDecay_(b[1], g, d, b_[1]);

            r.addRandnToWithDecay_(A[2], g, d, A_[2]);
            r.addRandnToWithDecay_(b[2], g, d, b_[2]);

            M32x32 Z1 = X.linearReluTransposed(A_[0], b_[0]);
            // Z1.addTo_(X, Z1);
            M32x32 Z2 = Z1.linearReluTransposed(A_[1], b_[1]);
            Z2.addTo_(Z1, Z2); // Test skip connection.
            M32x32 Z3 = Z2.linearTransposed(A_[2], b_[2]);
            // Z3.addTo_(Z2, Z3);

            // logMat('Z',Z);
            // logMat('Z+',Z.isPositive());
            // logMat('Y',Y);
            N32x32 score = Z3.isPositive().sumEq(Y);

            // logNum('score', score);

            // // Z1 = torch.relu(X @ A_[0] + b_[0])
            // // Z2 = torch.relu(Z1 @ A_[1] + b_[1])

            // // Output = (Z2[:,0] < Z2[:,1]).to(float)

            // // S = (y == Output).sum()

            if (score.gt(bestScore)) {
                logNum("score", score);
                bestScore = score;

                (A[0], A_[0]) = (A_[0], A[0]);
                (b[0], b_[0]) = (b_[0], b[0]);
                (A[1], A_[1]) = (A_[1], A[1]);
                (b[1], b_[1]) = (b_[1], b[1]);
            }
        }

        // logMat(X);
        // logMat(Y);

        // tensor([1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0,
        //         1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0,
        //         1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0,
        //         1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1,
        //         1, 0, 1, 1])
    }

    // function test_randn2() public {
    //     Random r = RandomLib.seed(0);
    //     M32x32 R = r.randn2(1, 10_000);

    //     logNum("min", R.min());
    //     logNum("max", R.max());

    //     // assertLt(R.abs(), N32x32Lib.ONE.mulInt(10));
    //     // assertGt(R, N32x32Lib.ZERO);

    //     assertApproxEqAbs(R.mean(), N32x32Lib.ZERO, N32x32Lib.ONE.divInt(100));
    //     assertApproxEqAbs(R.vari(), N32x32Lib.ONE, N32x32Lib.ONE.divInt(100));
    // }

    // function test_xxx(uint256 randomSeed) public {
    //     // function test_xxx() public {
    //     // Random r = RandomLib.seed(0);
    //     // uint256 randomSeed = r.randUint();

    //     int256 r1;
    //     assembly {
    //         // Sample a random normal variable.
    //         r1 := and(randomSeed, UINT32_MAX_X4) // Add masked halves together.
    //         r1 := add(r1, shr(32, and(randomSeed, not(UINT32_MAX_X4))))
    //         r1 := mul(r1, ONES_X4) // Multiply by `1 + (1 << 64) + (1 << 128) + (1 << 192)`.
    //         // r1 := sar(222, r1)
    //         r1 := shr(190, r1)
    //         // r1 := mul(4, r1) // The sum is located at bit pos 192. Multiply by `sqrt(N) = 4`.
    //         r1 := sub(r1, shl(32, 4)) // Subtract `8 * mean = 4 << 32`.
    //         r1 := sdiv(r1, 14878203147) // Divide by `sqrt(12) << 32`.
    //     }

    //     // Summing 8 packed uint64s.
    //     int256 sum1;

    //     unchecked {
    //         for (uint256 i; i < 8; i++) {
    //             // sum1 += int32(uint32(randomSeed >> i * 32));
    //             sum1 += int256(uint256(uint32(randomSeed >> i * 32)));
    //             // sum1 += int256(int64(uint64(randomSeed >> i * 32)));
    //         }
    //     }

    //     unchecked {
    //         sum1 = sum1 * 4 - (4 << 32);
    //         sum1 = sum1 / 14878203147;
    //     }

    //     assertEq(r1, sum1);
    // }

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
//         Random r = RandomLib.seed(0);

//         r.rand(128, 128);
//     }
// }
