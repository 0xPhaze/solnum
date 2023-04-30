// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "src/N32x32.sol";
import "./utils/TestHelper.sol";

contract TestN32x32Invariants is TestHelper {
    function test_fromUint_toUint(uint256 ua) public {
        if (ua > uint256(INT32_MAX)) {
            vm.expectRevert(N32x32_Overflow.selector);
        }

        assertEq(N32x32FromUint(ua).toUint(), ua);
    }

    function test_fromUint64_toUint64(uint64 ua) public {
        if (ua > uint64(uint256(INT32_MAX))) {
            vm.expectRevert(N32x32_Overflow.selector);
        }

        assertEq(N32x32FromUint64(ua).toUint64(), ua);
    }

    function test_fromUint32_toUint32(uint32 ua) public {
        if (ua > uint64(uint256(INT32_MAX))) {
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

        HALF_MAX.add(HALF_MAX).add(N32x32.wrap(2));
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
        a = bound(a, HALF_MIN, HALF_MAX);
        b = bound(b, HALF_MIN, HALF_MAX);

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
        a = bound(a, HALF_MIN, HALF_MAX);
        b = bound(b, HALF_MIN, HALF_MAX);

        assertEq(a.add(b), a.sub(ZERO.sub(b)));
    }

    /// @notice `a + b = a - (-b)` should hold or revert.
    function test_sub_r(N32x32 a, N32x32 b) public canRevert {
        assertEq(a.add(b), a.sub(ZERO.sub(b)));
    }

    /// @notice `a - b = -(b - a)` should hold for `a`, `b` in `[MIN/2, MAX/2]`.
    function test_sub_property(N32x32 a, N32x32 b) public {
        a = bound(a, HALF_MIN, HALF_MAX);
        b = bound(b, HALF_MIN, HALF_MAX);

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
        a = bound(a, MIN, HALF_MIN);
        b = bound(b, HALF_MIN.neg(), MAX);

        vm.expectRevert();

        a.sub(b).sub(N32x32.wrap(1));
    }

    /* ------------- add & sub ------------- */

    /// @notice `(a + b) - b = a` should hold for `a`, `b` in `[MIN/2, MAX/2]`.
    function test_add_sub(N32x32 a, N32x32 b) public {
        a = bound(a, HALF_MIN, HALF_MAX);
        b = bound(b, HALF_MIN, HALF_MAX);

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
        a = bound(a, HALF_MIN, HALF_MAX);

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
        a = bound(a, HALF_MIN, HALF_MAX);

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

    /* ------------- try ------------- */

    function test_tryAdd(N32x32 a, N32x32 b) public {
        (bool success,) = a.tryAdd(b);

        if (!success) vm.expectRevert(N32x32_Overflow.selector);

        a.add(b);
    }

    function test_trySub(N32x32 a, N32x32 b) public {
        (bool success,) = a.trySub(b);

        if (!success) vm.expectRevert(N32x32_Overflow.selector);

        a.sub(b);
    }

    function test_tryMul(N32x32 a, N32x32 b) public {
        (bool success,) = a.tryMul(b);

        if (!success) vm.expectRevert(N32x32_Overflow.selector);

        a.mul(b);
    }

    function test_tryDiv(N32x32 a, N32x32 b) public {
        b = bound(b, 1, MAX);

        (bool success,) = a.tryDiv(b);

        if (!success) vm.expectRevert(N32x32_Overflow.selector);

        a.div(b);
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

    function test_add_packed(int64 a1, int64 a2, int64 a3, int64 a4, int64 b1, int64 b2, int64 b3, int64 b4) public {
        // assertEqCall(
        //     abi.encodeCall(this.packedAdd, (pack(a1, a2, a3, a4), pack(b1, b2, b3, b4))),
        //     abi.encodeCall(this.simpleAdd, (a1, a2, a3, a4, b1, b2, b3, b4)),
        //     false
        // );
        assertEqCall(
            abi.encodeCall(this.packedAdd, (pack(a1, a2, a3, a4), pack(b1, b2, b3, b4))),
            abi.encodeCall(this.packedAdd2, (pack(a1, a2, a3, a4), pack(b1, b2, b3, b4))),
            false
        );
        assertEqCall(
            abi.encodeCall(this.packedAdd, (pack(a1, a2, a3, a4), pack(b1, b2, b3, b4))),
            abi.encodeCall(this.packedAdd3, (pack(a1, a2, a3, a4), pack(b1, b2, b3, b4))),
            false
        );
    }

    function test_gas_add_packed() public {
        (uint256 aX4, uint256 bX4) = (0, 0);

        packedAdd(aX4, bX4);
        packedAdd2(aX4, bX4);
        packedAdd3(aX4, bX4);
    }

    // function simpleAdd(
    //     int64 a1,
    //     int64 a2,
    //     int64 a3,
    //     int64 a4,
    //     int64 b1,
    //     int64 b2,
    //     int64 b3,
    //     int64 b4
    // )
    //     public
    //     pure
    //     returns (uint256)
    // {
    //     return pack(a1 + b1, a2 + b2, a3 + b3, a4 + b4);
    // }

    function packedAdd(uint256 aX4, uint256 bX4) public logs_gas returns (bool overflow, uint256 cX4) {
        assembly {
            let c4 := add(signextend(7, aX4), signextend(7, bX4))
            overflow := add(c4, INT64_SIGN)

            let c3 := add(signextend(7, shr(64, aX4)), signextend(7, shr(64, bX4)))
            overflow := or(overflow, add(c3, INT64_SIGN))

            let c2 := add(signextend(7, shr(128, aX4)), signextend(7, shr(128, bX4)))
            overflow := or(overflow, add(c2, INT64_SIGN))

            let c1 := add(sar(192, aX4), sar(192, bX4))
            overflow := or(overflow, add(c1, INT64_SIGN))

            overflow := gt(overflow, UINT64_MAX)

            cX4 := and(c4, UINT64_MAX)
            cX4 := or(cX4, shl(64, and(c3, UINT64_MAX)))
            cX4 := or(cX4, shl(128, and(c2, UINT64_MAX)))
            cX4 := or(cX4, shl(192, and(c1, UINT64_MAX)))
        }
    }

    function packedAdd2(uint256 aX4, uint256 bX4) public logs_gas returns (bool overflow, uint256 cX4) {
        unchecked {
            cX4 = (aX4 & MASK_2X4) + (bX4 & MASK_2X4) & MASK_2X4;
            cX4 = cX4 | (aX4 & ~MASK_2X4) + (bX4 & ~MASK_2X4) & ~MASK_2X4;

            // If signs are the same ~(aX4 ^ bX4), e.g. ~(1 ^ 1) = 1, ~(1 ^ 0) = 0,
            // and they now differ from the result (aX4 ^ cX4), there is overflow.
            // uint256 overflow = ((~(aX4 ^ bX4)) & (aX4 ^ cX4)) & INT64_SIGN_X4;
            overflow = ((~(aX4 ^ bX4)) & (aX4 ^ cX4)) & INT64_SIGN_X4 != 0;

            // if (overflow != 0) revert N32x32_Overflow();
        }
    }

    function packedAdd3(uint256 aX4, uint256 bX4) public logs_gas returns (bool overflow, uint256 cX4) {
        assembly {
            cX4 := and(add(and(aX4, MASK_2X4), and(bX4, MASK_2X4)), MASK_2X4)
            cX4 := or(cX4, and(add(and(aX4, not(MASK_2X4)), and(bX4, not(MASK_2X4))), not(MASK_2X4)))
            overflow := and(and(not(xor(aX4, bX4)), xor(aX4, cX4)), INT64_SIGN_X4)
        }
    }

    /* ------------- mul ------------- */

    function test_mul(int64 a, int64 b) public {
        a = int64(bound(a, 0, type(int64).max));
        // b = int64(bound(b, 0, type(int64).max));

        assertEqCall(abi.encodeCall(this.customMul, (a, b)), abi.encodeCall(this.simpleMul, (a, b)), false);
        // assertEqCall(abi.encodeCall(this.customMul2, (a, b)), abi.encodeCall(this.simpleMul, (a, b)), false);
        // assertEqCall(abi.encodeCall(this.customMul3, (a, b)), abi.encodeCall(this.simpleMul, (a, b)), false);
    }

    function test_case() public pure {
        int64 a = 1;
        int64 b = 1;
        customMul2(a, b);
    }

    function simpleMul(int64 a, int64 b) public pure returns (int64 c) {
        unchecked {
            int256 uc = int256(a) * b;

            if (uint256(uc) + uint256(int256(INT64_SIGN)) > UINT64_MAX) revert N32x32_Overflow();

            c = int64(uc);
        }
    }

    function customMul(int64 a, int64 b) public pure returns (int64 c) {
        unchecked {
            int256 uc;
            bool overflow;

            assembly {
                a := and(a, UINT64_MAX)
                b := and(b, UINT64_MAX)

                // uc := shr(32, mul(a, b))
                uc := mul(a, b)

                // overflow := gt(sub(signextend(15, uc), uMIN), UINT64_MAX)

                let shift := div(add(and(a, INT64_SIGN), and(b, INT64_SIGN)), 0x888)

                // if a > 0 and b > 0, then c < 0x8000
                // if a < 0 or b < 0, then 0x8000 <= c > 0x80000000
                // 0x0000 <= 0x8000 * 0x0000
                // 0x8000 <= 0x8000 * 0x0001
                // 0x0800 <= 0x0800 * 0x0010
                // if a < 0 and b < 0, then c > 0x80000000
                //                                          <=> 0xffffff40000000

                // do int64_min <= trunc(a * b) <= int64_max
                // 0x0000 = 0x8000 * 0x0000 good
                // 0x8000 = 0x8000 * 0x0001 good
                // 0x10000 = 0x8000 * 0x0002 bad
                // 0x1e000 = 0xf000 * 0x0002 good

                // sub by 0, divide by 0x8000 => 0 == Ok
                // sub by 0x8000, divide by (0x8000 * 0x7fff) => 0 == Ok
                // sub by 0x40000000 (0x8000 * 0x8000), divide by (0x8000 * 0x8000) => 0 == Ok

                // divide by 0: < 0x8000 == Ok
                // divide by 0x8000, sub 1 => < 0x8000 == Ok
                // divide by (0x8000 * 0x8000), sub by 1  => 0 == Ok

                // 0xffff0000

                overflow := gt(sub(shr(shift, uc), gt(shift, 0)), INT64_MAX)
                // overflow := gt(uc, INT64_MAX)
            }

            if (overflow) revert N32x32_Overflow();

            c = int64(uc);
        }
    }

    // function customMul3(int64 a, int64 b) public returns (int64 c) {
    //     unchecked {
    //         int256 uc;
    //         bool overflow;

    //         assembly {
    //             // uc := shr(32, mul(a, b))
    //             // + * + = -
    //             // - * - = -
    //             // false (same) and result is neg
    //             // true (diff) and result is pos
    //             // + * - = +
    //             // - * + = +

    //             uc := mul(and(a, UINT64_MAX), and(b, UINT64_MAX))
    //             // uc := mul(a, b)

    //             // overflow := gt(sub(signextend(15, uc), uMIN), UINT64_MAX)
    //             // overflow := gt(sub(uc, uMIN), UINT64_MAX)
    //         }
    //         console.log(
    //             "a",
    //             vm.toString(bytes32(uint256(int256(a)) & UINT64_MAX)),
    //             (a >> 63) & 1 == 1 ? "negative (1)" : "positive (0)"
    //         );
    //         console.log(
    //             "b",
    //             vm.toString(bytes32(uint256(int256(b)) & UINT64_MAX)),
    //             (b >> 63) & 1 == 1 ? "negative (1)" : "positive (0)"
    //         );
    //         console.log("input signs are", ((a >> 63) ^ (b >> 63)) & 1 == 1 ? "different (1)" : "same (0)");
    //         console.log("c", vm.toString(bytes32(uint256(uc))), (uc >> 63) & 1 == 1 ? "negative (1)" : "positive (0)");

    //         // (a ^ b) == c
    //         overflow = ((a >> 63) ^ (b >> 63) ^ (uc >> 63)) & 1 == 1;

    //         console.log("overflow", overflow ? "1" : "0");
    //         if (overflow) revert N32x32_Overflow();

    //         c = int64(uc);
    //     }
    // }

    function customMul2(int64 a, int64 b) public pure returns (int64 c) {
        unchecked {
            int256 uc;
            bool overflow;

            assembly {
                // a := and(a, UINT64_MAX)
                // b := and(b, UINT64_MAX)

                // uc := signextend(7, mul(a, b))
                uc := mul(a, b)
                // uc := mul(a, b)

                // XXX
                // Trying to detect overflow for truncated/packed int64s
                // Idea: use int256 overflow detection after shifting values to left by 24 bytes (192 bits)

                // // // Overflow, if `a != 0 && b != c / a`.
                overflow := iszero(or(iszero(a), eq(b, sdiv(shl(192, uc), shl(192, a)))))
                // overflow := iszero(or(iszero(a), eq(b, sdiv(uc, a))))

                // overflow := iszero(or(iszero(a), eq(b, shr(192, sdiv(shl(192, uc), shl(192, a))))))
                // overflow := iszero(or(iszero(a), eq(b, sdiv(uc, a))))

                // overflow := gt(shl(192, uc), uMIN), UINT64_MAX)
                // overflow := gt(sub(uc, uMIN), UINT64_MAX)

                // overflow := gt(sub(shl(128, uc), shl(128, uMIN)), shl(128, UINT64_MAX))
            }

            if (overflow) revert N32x32_Overflow();

            c = int64(uc);
            //
        }
    }

    // /* ------------- mulFixed ------------- */

    // function test_mul_fixed(int64 a, int64 b) public {
    //     assertEqCall(abi.encodeCall(this.customMulFixed, (a, b)), abi.encodeCall(this.simpleMulFixed, (a, b)), false);
    // }

    // function simpleMulFixed(int64 a, int64 b) public pure returns (int64 c) {
    //     unchecked {
    //         int256 uc = int256(a) * b >> 32;

    //         if (uint256(uc) + uint256(int256(INT64_SIGN)) > UINT64_MAX) revert N32x32_Overflow();

    //         c = int64(uc);
    //     }
    // }

    // function customMulFixed(int64 a, int64 b) public pure returns (int64 c) {
    //     unchecked {
    //         int256 uc;
    //         bool overflow;

    //         assembly {
    //             uc := signextend(11, shr(32, mul(a, b)))

    //             overflow := gt(sub(uc, uMIN), UINT64_MAX)
    //         }

    //         if (overflow) revert N32x32_Overflow();

    //         c = int64(uc);
    //     }
    // }

    /* ------------- mulScalar ------------- */

    function test_mulScalar(int64 a1, int64 a2, int64 a3, int64 a4, int64 s) public {
        assertEqCall(
            abi.encodeCall(this.customMulScalar, (pack(a1, a2, a3, a4), s)),
            abi.encodeCall(this.simpleMulScalar, (a1, a2, a3, a4, s)),
            false
        );
    }

    function simpleMulScalar(int64 a1, int64 a2, int64 a3, int64 a4, int64 s) public pure returns (uint256) {
        return pack(a1 * s, a2 * s, a3 * s, a4 * s);
    }

    function customMulScalar(uint256 aX4, int64 s) public pure returns (uint256 cX4) {
        unchecked {
            bool overflow;

            assembly {
                let c
                let carry

                c := mul(signextend(7, aX4), s)
                carry := add(signextend(15, c), INT64_SIGN)
                cX4 := and(c, UINT64_MAX)

                c := mul(signextend(7, shr(64, aX4)), s)
                carry := or(carry, add(signextend(15, c), INT64_SIGN))
                cX4 := or(cX4, shl(64, and(c, UINT64_MAX)))

                c := mul(signextend(7, shr(128, aX4)), s)
                carry := or(carry, add(signextend(15, c), INT64_SIGN))
                cX4 := or(cX4, shl(128, and(c, UINT64_MAX)))

                c := mul(signextend(7, shr(192, aX4)), s)
                carry := or(carry, add(signextend(15, c), INT64_SIGN))
                cX4 := or(cX4, shl(192, c))

                overflow := gt(carry, UINT64_MAX)
            }

            if (overflow) revert N32x32_Overflow();
        }
    }

    function customMulScalar2(uint256 aX4, int64 s) public pure returns (uint256 cX4) {
        unchecked {
            bool overflow;

            assembly {
                let c
                let carry
                let mask

                c := mul(signextend(7, aX4), s)
                carry := add(signextend(15, c), INT64_SIGN)
                cX4 := and(c, UINT64_MAX)

                c := mul(signextend(7, shr(64, aX4)), s)
                carry := or(carry, add(signextend(15, c), INT64_SIGN))
                cX4 := or(cX4, shl(64, and(c, UINT64_MAX)))

                c := mul(signextend(7, shr(128, aX4)), s)
                carry := or(carry, add(signextend(15, c), INT64_SIGN))
                cX4 := or(cX4, shl(128, and(c, UINT64_MAX)))

                c := mul(signextend(7, shr(192, aX4)), s)
                carry := or(carry, add(signextend(15, c), INT64_SIGN))
                cX4 := or(cX4, shl(192, c))

                overflow := gt(carry, UINT64_MAX)

                // ------------

                // // Extend the sign for int192 (24 = 23 + 1 bytes).
                // c := signextend(23, mul(a, b))

                // // Overflow, if `a != 0 && b != c / a`.
                // overflow := iszero(or(iszero(a), eq(b, sdiv(c, a))))

                // XXX This isn't working for some reason.
                // Idea: use same optimization as for addition.
                // then use upper reconstruction for overflow check.

                cX4 := and(mul(and(aX4, MASK_2X4), and(s, UINT64_MAX)), MASK_2X4)
                cX4 := or(cX4, and(mul(and(aX4, not(MASK_2X4)), and(s, UINT64_MAX)), not(MASK_2X4)))
            }

            if (overflow) revert N32x32_Overflow();
        }
    }

    /* ------------- mulScalarFixed ------------- */

    function test_mulScalarFixed(N32x32 a1, N32x32 a2, N32x32 a3, N32x32 a4, N32x32 s) public {
        assertEqCall(
            abi.encodeCall(this.customMulScalarFixed, (pack(a1, a2, a3, a4), s)),
            abi.encodeCall(this.simpleMulScalarFixed, (a1, a2, a3, a4, s)),
            false
        );
        // assertEqCall(
        //     abi.encodeCall(this.customMulScalarFixed2, (pack(a1, a2, a3, a4), s)),
        //     abi.encodeCall(this.simpleMulScalarFixed, (a1, a2, a3, a4, s)),
        //     false
        // );
    }

    function simpleMulScalarFixed(N32x32 a1, N32x32 a2, N32x32 a3, N32x32 a4, N32x32 s) public pure returns (uint256) {
        return pack(a1.mul(s), a2.mul(s), a3.mul(s), a4.mul(s));
    }

    function customMulScalarFixed(uint256 aX4, N32x32 s) public logs_gas returns (uint256 cX4) {
        bool overflow;

        assembly {
            let c := sar(32, mul(signextend(7, aX4), s))
            overflow := add(c, INT64_SIGN)
            cX4 := and(c, UINT64_MAX)

            c := sar(32, mul(signextend(7, shr(64, aX4)), s))
            overflow := or(overflow, add(c, INT64_SIGN))
            cX4 := or(cX4, shl(64, and(c, UINT64_MAX)))

            c := sar(32, mul(signextend(7, shr(128, aX4)), s))
            overflow := or(overflow, add(c, INT64_SIGN))
            cX4 := or(cX4, shl(128, and(c, UINT64_MAX)))

            c := sar(32, mul(sar(192, aX4), s))
            overflow := or(overflow, add(c, INT64_SIGN))
            cX4 := or(cX4, shl(192, and(c, UINT64_MAX)))

            overflow := gt(overflow, UINT64_MAX)

            // TODO:
            // cX4 := and(shr(32, mul(and(aX4, MASK_2X4), and(s, UINT64_MAX))), MASK_2X4)
            // cX4 := or(cX4, and(shr(32, mul(and(aX4, not(MASK_2X4)), and(s, UINT64_MAX))), not(MASK_2X4)))
        }

        if (overflow) revert N32x32_Overflow();
    }

    // If the product of two positive numbers exceeds max int, overflow
    // 0x1 * 0x7ffff = 0x7ffff

    // If the product of two negative numbers is less than max int, overflow

    // function customMulScalarFixed2(uint256 aX4, N32x32 s) public logs_gas returns (uint256 cX4) {
    //     bool overflow;

    //     assembly {
    //         let c := sar(32, mul(signextend(7, aX4), s))
    //         overflow := add(c, INT64_SIGN)
    //         cX4 := and(c, UINT64_MAX)

    //         c := sar(32, mul(signextend(7, shr(64, aX4)), s))
    //         overflow := or(overflow, add(c, INT64_SIGN))
    //         cX4 := or(cX4, shl(64, and(c, UINT64_MAX)))

    //         c := sar(32, mul(signextend(7, shr(128, aX4)), s))
    //         overflow := or(overflow, add(c, INT64_SIGN))
    //         cX4 := or(cX4, shl(128, and(c, UINT64_MAX)))

    //         c := sar(32, mul(sar(192, aX4), s))
    //         overflow := or(overflow, add(c, INT64_SIGN))
    //         cX4 := or(cX4, shl(192, and(c, UINT64_MAX)))

    //         overflow := gt(overflow, UINT64_MAX)

    //         // TODO:
    //         cX4 := and(shr(32, mul(and(aX4, MASK_2X4), and(s, UINT64_MAX))), MASK_2X4)
    //         cX4 := or(cX4, and(shl(32, mul(shr(64, and(aX4, not(MASK_2X4))), and(s, UINT64_MAX))), not(MASK_2X4)))
    //         // overflow := and(and(not(xor(aX4, bX4)), xor(aX4, cX4)), INT64_SIGN_X4)
    //     }

    //     if (overflow) revert N32x32_Overflow();
    // }
    // cX4 := and(add(and(aX4, MASK_2X4), and(bX4, MASK_2X4)), MASK_2X4)
    // cX4 := or(cX4, and(add(and(aX4, not(MASK_2X4)), and(bX4, not(MASK_2X4))), not(MASK_2X4)))
    // overflow := and(and(not(xor(aX4, bX4)), xor(aX4, cX4)), INT64_SIGN_X4)

    // // TODO
    // function customMulFixed(uint256 aX4, uint256 bX4) public logs_gas returns (bool overflow, uint256 cX4) {
    //     assembly {
    //         let c4 := add(signextend(7, aX4), signextend(7, bX4))
    //         overflow := add(c4, INT64_SIGN)

    //         let c3 := add(signextend(7, shr(64, aX4)), signextend(7, shr(64, bX4)))
    //         overflow := or(overflow, add(c3, INT64_SIGN))

    //         let c2 := add(signextend(7, shr(128, aX4)), signextend(7, shr(128, bX4)))
    //         overflow := or(overflow, add(c2, INT64_SIGN))

    //         let c1 := add(sar(192, aX4), sar(192, bX4))
    //         overflow := or(overflow, add(c1, INT64_SIGN))

    //         overflow := gt(overflow, UINT64_MAX)

    //         cX4 := and(c4, UINT64_MAX)
    //         cX4 := or(cX4, shl(64, and(c3, UINT64_MAX)))
    //         cX4 := or(cX4, shl(128, and(c2, UINT64_MAX)))
    //         cX4 := or(cX4, shl(192, and(c1, UINT64_MAX)))
    //     }
    // }

    /* ------------- dot ------------- */

    function trySimpleDot(
        int64 a1,
        int64 a2,
        int64 a3,
        int64 a4,
        int64 b1,
        int64 b2,
        int64 b3,
        int64 b4
    )
        public
        pure
        returns (bool success, int64 c)
    {
        int256 uc;

        unchecked {
            int256 c4 = int256(a4) * int256(b4);
            int256 c3 = int256(a3) * int256(b3);
            int256 c2 = int256(a2) * int256(b2);
            int256 c1 = int256(a1) * int256(b1);

            uc = c4 + c3 + c2 + c1;
        }

        success = !(uc < type(int64).min || uc > type(int64).max);

        c = int64(uc);
    }

    function simpleDot256(
        int256 a1,
        int256 a2,
        int256 a3,
        int256 a4,
        int256 b1,
        int256 b2,
        int256 b3,
        int256 b4
    )
        public
        pure
        returns (int256 c)
    {
        c = a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4;
    }

    function simpleDot(
        int256 a1,
        int256 a2,
        int256 a3,
        int256 a4,
        int256 b1,
        int256 b2,
        int256 b3,
        int256 b4
    )
        public
        logs_gas
        returns (int64 c)
    {
        unchecked {
            int256 uc = a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4;

            if (uc < type(int64).min || uc > type(int64).max) revert("overflow");

            c = int64(uc);
        }
    }

    function test_dot() public {
        test_dot(0, 0, 0, 0, 0, 0, 0, 0);
    }

    function test_dot(int64 a1, int64 a2, int64 a3, int64 a4, int64 b1, int64 b2, int64 b3, int64 b4) public {
        (bool success, int64 c) = trySimpleDot(a1, a2, a3, a4, b1, b2, b3, b4);
        if (success) {
            assertEq(int256(c), simpleDot256(a1, a2, a3, a4, b1, b2, b3, b4));
        }

        assertEqCall(
            abi.encodeCall(this.customDot, (pack(a1, a2, a3, a4), pack(b1, b2, b3, b4))),
            abi.encodeCall(this.simpleDot, (a1, a2, a3, a4, b1, b2, b3, b4)),
            false
        );
        assertEqCall(
            abi.encodeCall(this.customDot2, (pack(a1, a2, a3, a4), pack(b1, b2, b3, b4))),
            abi.encodeCall(this.simpleDot, (a1, a2, a3, a4, b1, b2, b3, b4)),
            false
        );
    }

    function customDot(uint256 aX4, uint256 bX4) public logs_gas returns (uint256 sum) {
        unchecked {
            bool overflow;

            assembly {
                let c
                let carry

                sum := mul(signextend(7, aX4), signextend(7, bX4))
                sum := add(sum, mul(signextend(7, shr(64, aX4)), signextend(7, shr(64, bX4))))
                sum := add(sum, mul(signextend(7, shr(128, aX4)), signextend(7, shr(128, bX4))))
                sum := add(sum, mul(sar(192, aX4), sar(192, bX4)))

                overflow := gt(add(sum, INT64_SIGN), UINT64_MAX)
            }

            if (overflow) revert N32x32_Overflow();
        }
    }

    function customDot2(uint256 aX4, uint256 bX4) public logs_gas returns (uint256 sum) {
        unchecked {
            bool overflow;

            assembly {
                // cX4 := and(add(and(aX4, MASK_2X4), and(bX4, MASK_2X4)), MASK_2X4)
                // cX4 := or(cX4, and(add(and(aX4, not(MASK_2X4)), and(bX4, not(MASK_2X4))), not(MASK_2X4)))
                // overflow := and(and(not(xor(aX4, bX4)), xor(aX4, cX4)), INT64_SIGN_X4)

                let c
                let carry

                sum :=
                    add(
                        shr(128, mul(or(shr(128, and(aX4, MASK_2X4)), shl(128, and(aX4, MASK_2X4))), and(bX4, MASK_2X4))),
                        shr(
                            128,
                            mul(
                                or(shr(192, and(aX4, not(MASK_2X4))), shl(64, and(aX4, not(MASK_2X4)))),
                                shr(64, and(bX4, not(MASK_2X4)))
                            )
                        )
                    )

                // c := mul(signextend(7, aX4), signextend(7, bX4))
                // sum := c

                // c := mul(signextend(7, shr(64, aX4)), signextend(7, shr(64, bX4)))
                // sum := add(sum, c)

                // c := mul(signextend(7, shr(128, aX4)), signextend(7, shr(128, bX4)))
                // sum := add(sum, c)

                // c := mul(sar(192, aX4), sar(192, bX4))
                // sum := add(sum, c)

                overflow := gt(add(sum, INT64_SIGN), UINT64_MAX)
            }

            if (overflow) revert N32x32_Overflow();
        }
    }

    function test_dott(int64 a1, int64 a2, int64 a3, int64 a4, int64 b1, int64 b2, int64 b3, int64 b4) public {
        assertEqCall(
            abi.encodeCall(this.customDott, (pack(a1, a2, a3, a4), pack(b1, b2, b3, b4))),
            abi.encodeCall(this.customDott2, (pack(a1, a2, a3, a4), pack(b1, b2, b3, b4))),
            false
        );
    }

    function customDott(uint256 aX4, uint256 bX4) public logs_gas returns (uint256 sum) {
        unchecked {
            bool overflow;

            assembly {
                let c
                let carry

                sum := mul(signextend(7, aX4), signextend(7, bX4))
                sum := add(sum, mul(signextend(7, shr(64, aX4)), signextend(7, shr(64, bX4))))
                sum := add(sum, mul(signextend(7, shr(128, aX4)), signextend(7, shr(128, bX4))))
                sum := add(sum, mul(sar(192, aX4), sar(192, bX4)))

                overflow := gt(add(sum, INT64_SIGN), UINT64_MAX)
            }

            if (overflow) revert N32x32_Overflow();
        }
    }

    function customDott2(uint256 aX4, uint256 bX4) public logs_gas returns (uint256 sum) {
        unchecked {
            bool overflow;

            assembly {
                // cX4 := and(add(and(aX4, MASK_2X4), and(bX4, MASK_2X4)), MASK_2X4)
                // cX4 := or(cX4, and(add(and(aX4, not(MASK_2X4)), and(bX4, not(MASK_2X4))), not(MASK_2X4)))
                // overflow := and(and(not(xor(aX4, bX4)), xor(aX4, cX4)), INT64_SIGN_X4)

                sum :=
                    add(
                        shr(128, mul(or(shr(128, and(aX4, MASK_2X4)), shl(128, and(aX4, MASK_2X4))), and(bX4, MASK_2X4))),
                        shr(
                            128,
                            mul(
                                or(shr(192, and(aX4, not(MASK_2X4))), shl(64, and(aX4, not(MASK_2X4)))),
                                shr(64, and(bX4, not(MASK_2X4)))
                            )
                        )
                    )

                overflow := gt(add(sum, INT64_SIGN), UINT64_MAX)
            }

            if (overflow) revert N32x32_Overflow();
        }
    }

    /* ------------- util ------------- */

    function pack(int64 a, int64 b, int64 c, int64 d) public pure returns (uint256 word) {
        word = ((uint64(a) & UINT64_MAX) << 192) | ((uint64(b) & UINT64_MAX) << 128) | ((uint64(c) & UINT64_MAX) << 64)
            | ((uint64(d) & UINT64_MAX));
    }

    function pack(N32x32 a, N32x32 b, N32x32 c, N32x32 d) internal pure returns (uint256 word) {
        word = (uint256(uint64(N32x32.unwrap(a))) << 192) | (uint256(uint64(N32x32.unwrap(b))) << 128)
            | (uint256(uint64(N32x32.unwrap(c))) << 64) | (uint256(uint64(N32x32.unwrap(d))));
    }
}

contract TestGas is TestHelper {
    // function test_perf_packedAdd(uint256 aX4, uint256 bX4) public pure returns (uint256 a) {
    //     for (uint256 i; i < 100; i++) {
    //         a = packedAdd(aX4, bX4);
    //     }
    // }

    function packedMul(uint256 aX4, uint256 bX4) public pure returns (uint256 cX4) {
        unchecked {
            cX4 = cX4 | (((((aX4 >> 192) & UINT64_MAX) * ((bX4 >> 192) & UINT64_MAX) & UINT64_MAX) >> 32) << 192);
            cX4 = cX4 | (((((aX4 >> 128) & UINT64_MAX) * ((bX4 >> 128) & UINT64_MAX) & UINT64_MAX) >> 32) << 128);
            cX4 = cX4 | (((((aX4 >> 64) & UINT64_MAX) * ((bX4 >> 64) & UINT64_MAX) & UINT64_MAX) >> 32) << 64);
            cX4 = cX4 | (((((aX4 >> 0) & UINT64_MAX) * ((bX4 >> 0) & UINT64_MAX) & UINT64_MAX) >> 32) << 0);
        }
    }

    // function packedAdd(uint256 aX4, uint256 bX4) public pure returns (uint256 cX4) {
    //     unchecked {
    //         cX4 = cX4 | ((((aX4 >> 192) & UINT64_MAX) + ((bX4 >> 192) & UINT64_MAX) & UINT64_MAX) << 192);
    //         cX4 = cX4 | ((((aX4 >> 128) & UINT64_MAX) + ((bX4 >> 128) & UINT64_MAX) & UINT64_MAX) << 128);
    //         cX4 = cX4 | ((((aX4 >> 64) & UINT64_MAX) + ((bX4 >> 64) & UINT64_MAX) & UINT64_MAX) << 64);
    //         cX4 = cX4 | ((((aX4 >> 0) & UINT64_MAX) + ((bX4 >> 0) & UINT64_MAX) & UINT64_MAX) << 0);
    //     }
    // }

    // function test_packedAdd() public {
    //     test_packedAdd(type(int64).max, 0, 0, 0, type(int64).max, 0, 0, 0);
    // }

    // uint256 result = pack(a1 + b1, a2 + bb1, 0 00, 0 + b4);

    // uint256 a = type(uint256).max + 1;

    // revert("123");

    // revert("faaalse");

    // console.log("result \t", vm.toString(bytes32(uint256(int256(result)))));

    // uint256 packed1 = pack(a1, a2, a3, a4);
    // uint256 packed2 = pack(b1, b2, b3, b4);

    // console.log("packed1 \t", vm.toString(bytes32(uint256(int256(packed1)))));
    // console.log("packed2 \t", vm.toString(bytes32(uint256(int256(packed2)))));
    // console.log("packed \t", vm.toString(bytes32(uint256(int256(packedAdd(packed1, packed2))))));

    // assertEq(packedAdd(a1, a2, a3, a4, b1, b2, b3, b4), simpleAdd(a1, a2, a3, a4, b1, b2, b3, b4));

    // assertEq(p + dp, ((a + da) << 64) | (b + db));
    // }

    // function test_differential_erfc(int256 x) public {
    //     bytes memory calldata1 = abi.encodeCall(this.erfc, (x));
    //     bytes memory calldata2 = abi.encodeCall(this.erfc_solidity, (x));

    //     // Make sure the functions behave EXACTLY the same in all cases.
    //     assertEqCall(address(this), calldata2, address(this), calldata1);
    // }
}
