// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "src/N32x32.sol";
import "./utils/TestHelper.sol";

contract TestN32x32Invariants is TestHelper {
    function test_fromUint_toUint(uint256 ua) public {
        if (ua > uint64(uMAX32)) {
            vm.expectRevert(N32x32_Overflow.selector);
        }

        assertEq(N32x32FromUint(ua).toUint(), ua);
    }

    function test_fromUint64_toUint64(uint64 ua) public {
        if (ua > uint64(uMAX32)) {
            vm.expectRevert(N32x32_Overflow.selector);
        }

        assertEq(N32x32FromUint64(ua).toUint64(), ua);
    }

    function test_fromUint32_toUint32(uint32 ua) public {
        if (ua > uint64(uMAX32)) {
            vm.expectRevert(N32x32_Overflow.selector);
        }

        assertEq(N32x32FromUint32(ua).toUint32(), ua);
    }

    function test_fromInt_toInt(int256 ua) public {
        if (ua < type(int32).min || ua > type(int32).max) {
            vm.expectRevert(N32x32_Overflow.selector);
        }

        assertEq(N32x32FromInt(ua).toInt(), ua);
    }

    function test_fromInt64_toInt64(int64 ua) public {
        if (ua < type(int32).min || ua > type(int32).max) {
            vm.expectRevert(N32x32_Overflow.selector);
        }

        assertEq(N32x32FromInt64(ua).toInt64(), ua);
    }

    function test_fromInt32_toInt32(int32 ua) public {
        if (ua < type(int32).min || ua > type(int32).max) {
            vm.expectRevert(N32x32_Overflow.selector);
        }

        assertEq(N32x32FromInt32(ua).toInt32(), ua);
    }

    /* ------------- add ------------- */

    /// @notice `a + 0 = a` should hold.
    function test_add(N32x32 a) public {
        assertEq(a.add(ZERO), a);
    }

    /// @notice `MAX/2 + MAX/2` should overflow.
    function test_add_revert_Overflow() public {
        vm.expectRevert(N32x32_Overflow.selector);

        MAX_HALF.add(MAX_HALF).add(N32x32.wrap(2));
    }

    /// @notice `(a + b) + 1` should overflow for `a` in `(0, MAX]`, `b` in `[MAX-a, MAX]`.
    function test_add_revert_Overflow(N32x32 a, N32x32 b) public {
        a = bound(a, ZERO, MAX);
        b = bound(b, MAX.sub(a), MAX);

        vm.expectRevert(N32x32_Overflow.selector);

        a.add(b).add(N32x32.wrap(1));
    }

    /// @notice `(a + b) - 1` should underflow for `a` in `[MIN, 0]`, `b` in `[MIN, MIN-a]`.
    function test_add_revert_Underflow(N32x32 a, N32x32 b) public {
        a = bound(a, MIN, ZERO);
        b = bound(b, MIN, MIN.sub(a));

        vm.expectRevert(N32x32_Overflow.selector);

        a.add(b).add(N32x32.wrap(-1));
    }

    /// @notice `a + b = b + a` should hold for `a`, `b` in `[MIN/2, MAX/2]`.
    function test_add_commutative(N32x32 a, N32x32 b) public {
        a = bound(a, MIN_HALF, MAX_HALF);
        b = bound(b, MIN_HALF, MAX_HALF);

        assertEq(a.add(b), b.add(a));
    }

    /// @notice `a + b = b + a` should hold or revert.
    function test_add_commutative_r(N32x32 a, N32x32 b) public canRevert {
        assertEq(a.add(b), b.add(a));
    }

    /// @notice `(a + b) + c = a + (b + c)` should hold or revert.
    function test_add_associative_r(N32x32 a, N32x32 b, N32x32 c) public canRevert {
        assertEq(a.add(b).add(c), a.add(b.add(c)));
    }

    /* ------------- sub ------------- */

    /// @notice `a + b = a - (-b)` should hold for `a`, `b` in `[MIN/2, MAX/2]`.
    function test_sub(N32x32 a, N32x32 b) public {
        a = bound(a, MIN_HALF, MAX_HALF);
        b = bound(b, MIN_HALF, MAX_HALF);

        assertEq(a.add(b), a.sub(ZERO.sub(b)));
    }

    /// @notice `a + b = a - (-b)` should hold or revert.
    function test_sub_r(N32x32 a, N32x32 b) public canRevert {
        assertEq(a.add(b), a.sub(ZERO.sub(b)));
    }

    /// @notice `a - b = -(b - a)` should hold for `a`, `b` in `[MIN/2, MAX/2]`.
    function test_sub_property(N32x32 a, N32x32 b) public {
        a = bound(a, MIN_HALF, MAX_HALF);
        b = bound(b, MIN_HALF, MAX_HALF);

        assertEq(a.sub(b), ZERO.sub(b.sub(a)));
    }

    /// @notice `a - b = -(b - a)` should hold or revert.
    function test_sub_property_r(N32x32 a, N32x32 b) public canRevert {
        assertEq(a.sub(b), ZERO.sub(b.sub(a)));
    }

    /// @notice `a - b` should overflow for `a` in `[0, MAX]`, `b` in `[MIN, MIN+a]`.
    function test_sub_revert_Overflow(N32x32 a, N32x32 b) public {
        a = bound(a, ZERO, MAX);
        b = bound(b, MIN, MIN.add(a));

        vm.expectRevert(N32x32_Overflow.selector);

        a.sub(b);
    }

    /// @notice `(a - b) - 1` should underflow for `a` in `[MIN, MIN/2]`, `b` in `(MIN/2, MAX]`.
    function test_sub_revert_Underflow(N32x32 a, N32x32 b) public {
        a = bound(a, MIN, MIN_HALF);
        b = bound(b, MIN_HALF.neg(), MAX);

        vm.expectRevert();

        a.sub(b).sub(N32x32.wrap(1));
    }

    /* ------------- add & sub ------------- */

    /// @notice `(a + b) - b = a` should hold for `a`, `b` in `[MIN/2, MAX/2]`.
    function test_add_sub(N32x32 a, N32x32 b) public {
        a = bound(a, MIN_HALF, MAX_HALF);
        b = bound(b, MIN_HALF, MAX_HALF);

        assertEq(a.add(b).sub(b), a);
        assertEq(a.sub(b).add(b), a);
    }

    /// @notice `(a + b) - b = a` should hold or revert.
    function test_add_sub_r(N32x32 a, N32x32 b) public canRevert {
        assertEq(a.add(b).sub(b), a);
    }

    /// @notice `(a - b) + b = a` should hold or revert.
    function test_sub_add_r(N32x32 a, N32x32 b) public canRevert {
        assertEq(a.sub(b).add(b), a);
    }

    /* ------------- neg ------------- */

    /// @notice `-MIN` should overflow.
    function test_neg_revert_Overflow() public {
        vm.expectRevert();

        MIN.neg();
    }

    /// @notice `-a = 0 - a` should hold for `a` in `(MIN, MAX]`.
    function test_neg(N32x32 a) public {
        a = bound(a, MAX.neg(), MAX);

        assertEq(a.neg(), ZERO.sub(a));
    }

    /* ------------- sign ------------- */

    /// @notice `sign(a) = 1` should hold for `a` in `[0, MAX]`.
    function test_sign(N32x32 a) public {
        a = bound(a, ZERO, MAX);

        assertEq(a.sign(), ONE);
    }

    /// @notice `sign(a) = -1` should hold for `a` in `[MIN, 0)`.
    function test_sign_neg(N32x32 a) public {
        a = bound(a, MIN, -1);

        assertEq(a.sign(), NEG_ONE);
    }

    /* ------------- abs ------------- */

    /// @notice `|a| = a` should hold for `a` in `[0, MAX]`.
    function test_abs(N32x32 a) public {
        a = bound(a, ZERO, MAX);

        assertEq(a.abs(), a);
    }

    /// @notice `|a| = -a` should hold for `a` in `(MIN, 0]`.
    function test_abs_neg(N32x32 a) public {
        a = bound(a, MAX.neg(), ZERO);

        assertEq(a.abs(), a.neg());
    }

    /// @notice `|MIN|` should overflow.
    function test_abs_revert_Overflow() public {
        vm.expectRevert();

        MIN.abs();
    }

    /* ------------- mul ------------- */

    /// @notice `a * 1 = a` should hold.
    function test_mul_by_one(N32x32 a) public {
        assertEq(a.mul(ONE), a);
    }

    /// @notice `a * 0 = 0` should hold.
    function test_mul_by_zero(N32x32 a) public {
        assertEq(a.mul(ZERO), ZERO);
    }

    /// @notice `a * 2 = a + a` should hold for `a` in `[MIN/2, MAX/2]`..
    function test_mul_by_two(N32x32 a) public {
        a = bound(a, MIN_HALF, MAX_HALF);

        assertEq(a.mul(TWO), a.add(a));
    }

    /// @notice `a * (-1) = -a` should hold for `a` in `(MIN, MAX]`.
    function test_mul_by_neg_one(N32x32 a) public {
        a = bound(a, MAX.neg(), MAX);

        assertEq(a.mul(NEG_ONE), a.neg());
    }

    /// @notice `a * b = b * a` should hold or revert.
    function test_mul_commutative(N32x32 a, N32x32 b) public canRevert {
        assertEq(a.mul(b), b.mul(a));
    }

    /// @notice `(a * b) * c = a * (b * c)` should hold or revert.
    function test_mul_associative(N32x32 a, N32x32 b, N32x32 c) public canRevert {
        // Bounding to third root of MAX to prevent overflow rejects.
        a = bound(a, ONE, N32x32.wrap(1290 << 32));
        b = bound(b, ONE, N32x32.wrap(1290 << 32));
        c = bound(c, ONE, N32x32.wrap(1290 << 32));

        // Approximate due to rounding errors.
        // todo: investigate.
        assertApproxEqRel(a.mul(b.mul(c)), a.mul(b).mul(c), 0.000000001e18);
    }

    /// @notice `a * (b + c) = a * b + a * c` should hold or revert.
    function test_mul_distributive(N32x32 a, N32x32 b, N32x32 c) public canRevert {
        // Approximate due to rounding errors.
        assertApproxEqAbs(a.mul(b.add(c)), a.mul(b).add(a.mul(c)), 1);
    }

    /// @notice `a * b` should overflow for `a` in `(0, MAX)`, `b` in `(MAX/a, MAX]`.
    function test_mul_revert_Overflow(N32x32 a, N32x32 b) public {
        a = bound(a, ONE.add(N32x32.wrap(1)), MAX);
        b = bound(b, MAX.divUp(a).add(N32x32.wrap(1)), MAX);

        vm.expectRevert();

        a.mul(b);
    }

    /* ------------- div ------------- */

    /// @notice `a / 1 = a` should hold.
    function test_div_by_one(N32x32 a) public {
        assertEq(a.div(ONE), a);
    }

    /// @notice `a / 0` should revert.
    function test_div_by_zero(N32x32 a) public {
        vm.expectRevert();

        a.div(ZERO);
    }

    /// @notice `(a * 2) / 2 = a` should hold for `a` in `[MIN/2, MAX/2]`.
    function test_div_by_two(N32x32 a) public {
        a = bound(a, MIN_HALF, MAX_HALF);

        assertEq(a.mul(TWO).div(TWO), a);
    }

    /// @notice `a / (-1) = -a` should hold for `a` in `(MIN, MAX]`.
    function test_div_by_neg_one(N32x32 a) public {
        a = bound(a, MAX.neg(), MAX);

        assertEq(a.div(NEG_ONE), a.neg());
    }

    /// @notice `(a * b) / b = a` should approx. hold or revert.
    function test_mul_div(N32x32 a, N32x32 b) public canRevert {
        assertApproxEqAbs(a.mul(b).div(b), a, ONE);
        assertApproxEqAbs(a.div(b).mul(b), a, ONE);
    }

    /// @notice `(a * b) / b = a` should approx. hold or revert for
    ///         `|a|` in `[ONE, MAX]`, `|a*b|` in `[|a|, MAX]`
    function test_mul_div_precision(N32x32 a, N32x32 b) public canRevert {
        a = bound(a.abs(), ONE, MAX).mul(a.sign());
        b = bound(b.abs(), ONE, MAX.div(a.abs())).mul(b.sign());

        assertApproxEqAbs(a.mul(b).div(b), a, 1);
    }

    /// @notice `(a / b) * b = a` should approx. hold or revert for
    ///         `|a|` in `[0, ONE]`, `|b|` in `[|a/MAX|, ONE]`
    function test_div_mul_precision(N32x32 a, N32x32 b) public canRevert {
        a = bound(a.abs(), ZERO, ONE).mul(a.sign());
        b = bound(b.abs(), a.abs().div(MAX), ONE).mul(b.sign());

        assertApproxEqAbs(a.div(b).mul(b), a, 1);
    }

    /* ------------- divUp ------------- */

    /// @notice The result of `divUp` should always be greater than or equal to `div`.
    function test_divUp(N32x32 a, N32x32 b) public canRevert {
        N32x32 c = a.div(b);
        N32x32 d = a.divUp(b);

        assertGte(d, c);
        assertApproxEqAbs(c, d, 2);
    }
}

contract TestGasN32x32 is TestHelper {
    function test_perf_add(N32x32 a, N32x32 b) public canRevert {
        a.add(b);
    }

    function test_perf_sub(N32x32 a, N32x32 b) public canRevert {
        a.sub(b);
    }

    function test_perf_mul(N32x32 a, N32x32 b) public canRevert {
        a.mul(b);
    }

    function test_perf_div(N32x32 a, N32x32 b) public canRevert {
        a.div(b);
    }
}

contract TestN32x32Differential is TestHelper {
    /* ------------- add ------------- */

    function test_add_packed(int64 a1, int64 b1, int64 c1, int64 d1, int64 a2, int64 b2, int64 c2, int64 d2) public {
        assertEqCall(
            abi.encodeCall(this.packedAdd, (pack(a1, b1, c1, d1), pack(a2, b2, c2, d2))),
            abi.encodeCall(this.simpleAdd, (a1, b1, c1, d1, a2, b2, c2, d2)),
            false
        );
    }

    function simpleAdd(
        int64 a1,
        int64 b1,
        int64 c1,
        int64 d1,
        int64 a2,
        int64 b2,
        int64 c2,
        int64 d2
    )
        public
        pure
        returns (uint256)
    {
        return pack(a1 + a2, b1 + b2, c1 + c2, d1 + d2);
    }

    function packedAdd(uint256 p1, uint256 p2) public pure returns (uint256 res) {
        unchecked {
            res = (p1 & UINT64_MASK_X2) + (p2 & UINT64_MASK_X2) & UINT64_MASK_X2;
            res = res | (p1 & UINT64_MASK_2X) + (p2 & UINT64_MASK_2X) & UINT64_MASK_2X;

            // If signs are the same ~(p1 ^ p2), e.g. ~(1 ^ 1) = 1, ~(1 ^ 0) = 0,
            // and they now differ from the result (p1 ^ res), there is overflow.
            // uint256 overflow = ((~(p1 ^ p2)) & (p1 ^ res)) & SIGN_MASK_X4;
            uint256 overflow = ((~(p1 ^ p2)) & (p1 ^ res)) & SIGN_MASK_X4;

            if (overflow != 0) revert("Overflow");

            // naive!
            // res = res | ((((p1 >> 192) & UINT64_MASK) + ((p2 >> 192) & UINT64_MASK) & UINT64_MASK) << 192);
            // res = res | ((((p1 >> 128) & UINT64_MASK) + ((p2 >> 128) & UINT64_MASK) & UINT64_MASK) << 128);
            // res = res | ((((p1 >> 64) & UINT64_MASK) + ((p2 >> 64) & UINT64_MASK) & UINT64_MASK) << 64);
            // res = res | ((((p1 >> 0) & UINT64_MASK) + ((p2 >> 0) & UINT64_MASK) & UINT64_MASK) << 0);
        }
    }

    /* ------------- mul ------------- */

    function test_mul(int64 a, int64 b) public {
        assertEqCall(abi.encodeCall(this.customMul, (a, b)), abi.encodeCall(this.simpleMul, (a, b)), false);
    }

    function simpleMul(int64 a, int64 b) public pure returns (int64 c) {
        unchecked {
            int256 uc = int256(a) * b;
            // int256 uc = int256(a) * b >> 32;

            if (uint256(uc) - uint256(int256(uMIN)) > UINT64_MASK) revert N32x32_Overflow();
            // if (uint256(uc) + uNEG_MIN > UINT64_MASK) revert N32x32_Overflow();

            c = int64(uc);
        }
    }

    function customMul(int64 a, int64 b) public pure returns (int64 c) {
        unchecked {
            int256 uc;
            bool overflow;

            assembly {
                // uc := shr(32, mul(a, b))
                uc := mul(a, b)

                // overflow := gt(sub(signextend(15, uc), uMIN), UINT64_MASK)
                overflow := gt(sub(uc, uMIN), UINT64_MASK)
            }

            if (overflow) revert N32x32_Overflow();

            c = int64(uc);
        }
    }

    function customMul2(int64 a, int64 b) public pure returns (int64 c) {
        unchecked {
            int256 uc;
            bool overflow;

            assembly {
                uc := mul(a, b)

                overflow := gt(sub(shl(128, uc), shl(128, uMIN)), shl(128, UINT64_MASK))
            }

            if (overflow) revert N32x32_Overflow();

            c = int64(uc);
        }
    }

    /* ------------- mulFixed ------------- */

    function test_mul_fixed(int64 a, int64 b) public {
        assertEqCall(abi.encodeCall(this.customMulFixed, (a, b)), abi.encodeCall(this.simpleMulFixed, (a, b)), false);
    }

    function simpleMulFixed(int64 a, int64 b) public pure returns (int64 c) {
        unchecked {
            int256 uc = int256(a) * b >> 32;

            if (uint256(uc) - uint256(int256(uMIN)) > UINT64_MASK) revert N32x32_Overflow();

            c = int64(uc);
        }
    }
    // function simpleMulFixed(int64 a, int64 b) public pure returns (int64 c) {
    //     unchecked {
    //         int256 uc = int256(int96(uint96(uint128(uint64(a)) * uint128(uint64(b)) >> 32)));

    //         if (uint256(uc) - uint256(int256(uMIN)) > UINT64_MASK) revert N32x32_Overflow();

    //         c = int64(uc);
    //     }
    // }

    function customMulFixed(int64 a, int64 b) public pure returns (int64 c) {
        unchecked {
            int256 uc;
            bool overflow;

            assembly {
                uc := signextend(11, shr(32, mul(a, b)))

                overflow := gt(sub(uc, uMIN), UINT64_MASK)
            }

            if (overflow) revert N32x32_Overflow();

            c = int64(uc);
        }
    }

    /* ------------- mulPacked ------------- */

    function test_mul_packed(int64 a, int64 b, int64 c, int64 d, int64 s) public {
        assertEqCall(
            abi.encodeCall(this.customMulPacked2, (pack(a, b, c, d), s)),
            abi.encodeCall(this.simpleMulPacked, (a, b, c, d, s)),
            false
        );
    }

    function customMulPacked(uint256 aX4, int64 s) public pure returns (uint256 cX4) {
        unchecked {
            bool overflow;

            assembly {
                let c
                let carry

                c := mul(signextend(7, aX4), s)
                carry := sub(signextend(15, c), uMIN)
                cX4 := and(c, UINT64_MASK)

                c := mul(signextend(7, shr(64, aX4)), s)
                carry := or(carry, sub(signextend(15, c), uMIN))
                cX4 := or(cX4, shl(64, and(c, UINT64_MASK)))

                c := mul(signextend(7, shr(128, aX4)), s)
                carry := or(carry, sub(signextend(15, c), uMIN))
                cX4 := or(cX4, shl(128, and(c, UINT64_MASK)))

                c := mul(signextend(7, shr(192, aX4)), s)
                carry := or(carry, sub(signextend(15, c), uMIN))
                cX4 := or(cX4, shl(192, c))

                overflow := gt(carry, UINT64_MASK)
            }

            if (overflow) revert N32x32_Overflow();
        }
    }

    function customMulPacked2(uint256 aX4, int64 s) public pure returns (uint256 cX4) {
        unchecked {
            bool overflow;

            assembly {
                let c
                let carry
                let mask

                c := shl(128, mul(signextend(7, aX4), s))
                carry := sub(c, shl(128, uMIN))
                cX4 := and(shr(128, c), UINT64_MASK)

                mask := shl(64, UINT64_MASK)
                c := shl(64, mul(signextend(15, and(aX4, mask)), s))
                carry := or(carry, sub(c, shl(128, uMIN)))
                cX4 := or(cX4, and(shr(64, c), mask))

                mask := shl(128, UINT64_MASK)
                c := mul(signextend(23, and(aX4, mask)), s)
                carry := or(carry, sub(c, shl(128, uMIN)))
                cX4 := or(cX4, and(c, mask))

                c := mul(signextend(23, and(shr(64, aX4), mask)), s)
                carry := or(carry, sub(c, shl(128, uMIN)))
                cX4 := or(cX4, shl(64, and(c, mask)))

                overflow := gt(shr(128, carry), UINT64_MASK)
            }

            if (overflow) revert N32x32_Overflow();
        }
    }

    function simpleMulPacked(int64 a, int64 b, int64 c, int64 d, int64 s) public pure returns (uint256) {
        return pack(a * s, b * s, c * s, d * s);
    }

    /* ------------- util ------------- */

    function pack(int64 a, int64 b, int64 c, int64 d) public pure returns (uint256 word) {
        word = ((uint64(a) & UINT64_MASK) << 192) | ((uint64(b) & UINT64_MASK) << 128)
            | ((uint64(c) & UINT64_MASK) << 64) | ((uint64(d) & UINT64_MASK));
    }
}

uint256 constant UINT64_SIGN_MASK = 0x8000000000000000;
uint256 constant UINT64_MASK_X2 = 0x0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff;
uint256 constant UINT64_MASK_2X = 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000;
uint256 constant SIGN_MASK_X4 = 0x8000000000000000800000000000000080000000000000008000000000000000;

contract TestGas is TestHelper {
    // function test_perf_packedAdd(uint256 p1, uint256 p2) public pure returns (uint256 a) {
    //     for (uint256 i; i < 100; i++) {
    //         a = packedAdd(p1, p2);
    //     }
    // }

    function packedMul(uint256 p1, uint256 p2) public pure returns (uint256 res) {
        unchecked {
            res = res | (((((p1 >> 192) & UINT64_MASK) * ((p2 >> 192) & UINT64_MASK) & UINT64_MASK) >> 32) << 192);
            res = res | (((((p1 >> 128) & UINT64_MASK) * ((p2 >> 128) & UINT64_MASK) & UINT64_MASK) >> 32) << 128);
            res = res | (((((p1 >> 64) & UINT64_MASK) * ((p2 >> 64) & UINT64_MASK) & UINT64_MASK) >> 32) << 64);
            res = res | (((((p1 >> 0) & UINT64_MASK) * ((p2 >> 0) & UINT64_MASK) & UINT64_MASK) >> 32) << 0);
        }
    }

    // function packedAdd(uint256 p1, uint256 p2) public pure returns (uint256 res) {
    //     unchecked {
    //         res = res | ((((p1 >> 192) & UINT64_MASK) + ((p2 >> 192) & UINT64_MASK) & UINT64_MASK) << 192);
    //         res = res | ((((p1 >> 128) & UINT64_MASK) + ((p2 >> 128) & UINT64_MASK) & UINT64_MASK) << 128);
    //         res = res | ((((p1 >> 64) & UINT64_MASK) + ((p2 >> 64) & UINT64_MASK) & UINT64_MASK) << 64);
    //         res = res | ((((p1 >> 0) & UINT64_MASK) + ((p2 >> 0) & UINT64_MASK) & UINT64_MASK) << 0);
    //     }
    // }

    // function test_packedAdd() public {
    //     test_packedAdd(type(int64).max, 0, 0, 0, type(int64).max, 0, 0, 0);
    // }

    // uint256 result = pack(a1 + a2, b1 + b2, c1 + c2, d1 + d2);

    // uint256 a = type(uint256).max + 1;

    // revert("123");

    // revert("faaalse");

    // console.log("result \t", vm.toString(bytes32(uint256(int256(result)))));

    // uint256 packed1 = pack(a1, b1, c1, d1);
    // uint256 packed2 = pack(a2, b2, c2, d2);

    // console.log("packed1 \t", vm.toString(bytes32(uint256(int256(packed1)))));
    // console.log("packed2 \t", vm.toString(bytes32(uint256(int256(packed2)))));
    // console.log("packed \t", vm.toString(bytes32(uint256(int256(packedAdd(packed1, packed2))))));

    // assertEq(packedAdd(a1, b1, c1, d1, a2, b2, c2, d2), simpleAdd(a1, b1, c1, d1, a2, b2, c2, d2));

    // assertEq(p + dp, ((a + da) << 64) | (b + db));
    // }

    // function test_differential_erfc(int256 x) public {
    //     bytes memory calldata1 = abi.encodeCall(this.erfc, (x));
    //     bytes memory calldata2 = abi.encodeCall(this.erfc_solidity, (x));

    //     // Make sure the functions behave EXACTLY the same in all cases.
    //     assertEqCall(address(this), calldata2, address(this), calldata1);
    // }
}
