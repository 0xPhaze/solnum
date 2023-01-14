// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "src/SN32x32.sol";
import "./TestHelper.sol";

contract TestSN32x32 is TestHelper {
    /* ------------- add ------------- */

    /// @notice `a + 0 = a` should hold.
    function test_add(SN32x32 a) public {
        assertEq(a.add(ZERO), a);
    }

    /// @notice `MAX/2 + MAX/2` should overflow.
    function test_add_revert_Overflow() public {
        vm.expectRevert(Overflow.selector);

        MAX_HALF.add(MAX_HALF).add(wrap(2));
    }

    /// @notice `(a + b) + 1` should overflow for `a` in `(0, MAX]`, `b` in `[MAX-a, MAX]`.
    function test_add_revert_Overflow(SN32x32 a, SN32x32 b) public {
        a = bound(a, ZERO, MAX);
        b = bound(b, MAX.sub(a), MAX);

        vm.expectRevert(Overflow.selector);

        a.add(b).add(wrap(1));
    }

    /// @notice `(a + b) - 1` should underflow for `a` in `[MIN, 0]`, `b` in `[MIN, MIN-a]`.
    function test_add_revert_Underflow(SN32x32 a, SN32x32 b) public {
        a = bound(a, MIN, ZERO);
        b = bound(b, MIN, MIN.sub(a));

        vm.expectRevert(Overflow.selector);

        a.add(b).add(wrap(-1));
    }

    /// @notice `a + b = b + a` should hold for `a`, `b` in `[MIN/2, MAX/2]`.
    function test_add_commutative(SN32x32 a, SN32x32 b) public {
        a = bound(a, MIN_HALF, MAX_HALF);
        b = bound(b, MIN_HALF, MAX_HALF);

        assertEq(a.add(b), b.add(a));
    }

    /// @notice `a + b = b + a` should hold or revert.
    function test_add_commutative_r(SN32x32 a, SN32x32 b) public canRevert {
        assertEq(a.add(b), b.add(a));
    }

    /// @notice `(a + b) + c = a + (b + c)` should hold or revert.
    function test_add_associative_r(SN32x32 a, SN32x32 b, SN32x32 c) public canRevert {
        assertEq(a.add(b).add(c), a.add(b.add(c)));
    }

    /* ------------- sub ------------- */

    /// @notice `a + b = a - (-b)` should hold for `a`, `b` in `[MIN/2, MAX/2]`.
    function test_sub(SN32x32 a, SN32x32 b) public {
        a = bound(a, MIN_HALF, MAX_HALF);
        b = bound(b, MIN_HALF, MAX_HALF);

        assertEq(a.add(b), a.sub(ZERO.sub(b)));
    }

    /// @notice `a + b = a - (-b)` should hold or revert.
    function test_sub_r(SN32x32 a, SN32x32 b) public canRevert {
        assertEq(a.add(b), a.sub(ZERO.sub(b)));
    }

    /// @notice `a - b = -(b - a)` should hold for `a`, `b` in `[MIN/2, MAX/2]`.
    function test_sub_property(SN32x32 a, SN32x32 b) public {
        a = bound(a, MIN_HALF, MAX_HALF);
        b = bound(b, MIN_HALF, MAX_HALF);

        assertEq(a.sub(b), ZERO.sub(b.sub(a)));
    }

    /// @notice `a - b = -(b - a)` should hold or revert.
    function test_sub_property_r(SN32x32 a, SN32x32 b) public canRevert {
        assertEq(a.sub(b), ZERO.sub(b.sub(a)));
    }

    /// @notice `a - b` should overflow for `a` in `[0, MAX]`, `b` in `[MIN, MIN+a]`.
    function test_sub_revert_Overflow(SN32x32 a, SN32x32 b) public {
        a = bound(a, ZERO, MAX);
        b = bound(b, MIN, MIN.add(a));

        vm.expectRevert(Overflow.selector);

        a.sub(b);
    }

    /// @notice `(a - b) - 1` should underflow for `a` in `[MIN, MIN/2]`, `b` in `(MIN/2, MAX]`.
    function test_sub_revert_Underflow(SN32x32 a, SN32x32 b) public {
        a = bound(a, MIN, MIN_HALF);
        b = bound(b, MIN_HALF.neg(), MAX);

        vm.expectRevert();

        a.sub(b).sub(wrap(1));
    }

    /* ------------- add & sub ------------- */

    /// @notice `(a + b) - b = a` should hold for `a`, `b` in `[MIN/2, MAX/2]`.
    function test_add_sub(SN32x32 a, SN32x32 b) public {
        a = bound(a, MIN_HALF, MAX_HALF);
        b = bound(b, MIN_HALF, MAX_HALF);

        assertEq(a.add(b).sub(b), a);
        assertEq(a.sub(b).add(b), a);
    }

    /// @notice `(a + b) - b = a` should hold or revert.
    function test_add_sub_r(SN32x32 a, SN32x32 b) public canRevert {
        assertEq(a.add(b).sub(b), a);
    }

    /// @notice `(a - b) + b = a` should hold or revert.
    function test_sub_add_r(SN32x32 a, SN32x32 b) public canRevert {
        assertEq(a.sub(b).add(b), a);
    }

    /* ------------- neg ------------- */

    /// @notice `-MIN` should overflow.
    function test_neg_revert_Overflow() public {
        vm.expectRevert();

        MIN.neg();
    }

    /// @notice `-a = 0 - a` should hold for `a` in `(MIN, MAX]`.
    function test_neg(SN32x32 a) public {
        a = bound(a, MAX.neg(), MAX);

        assertEq(a.neg(), ZERO.sub(a));
    }

    /* ------------- sign ------------- */

    /// @notice `sign(a) = 1` should hold for `a` in `[0, MAX]`.
    function test_sign(SN32x32 a) public {
        a = bound(a, ZERO, MAX);

        assertEq(a.sign(), ONE);
    }

    /// @notice `sign(a) = -1` should hold for `a` in `[MIN, 0)`.
    function test_sign_neg(SN32x32 a) public {
        a = bound(a, MIN, -1);

        assertEq(a.sign(), NEG_ONE);
    }

    /* ------------- abs ------------- */

    /// @notice `|a| = a` should hold for `a` in `[0, MAX]`.
    function test_abs(SN32x32 a) public {
        a = bound(a, ZERO, MAX);

        assertEq(a.abs(), a);
    }

    /// @notice `|a| = -a` should hold for `a` in `(MIN, 0]`.
    function test_abs_neg(SN32x32 a) public {
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
    function test_mul_by_one(SN32x32 a) public {
        assertEq(a.mul(ONE), a);
    }

    /// @notice `a * 0 = 0` should hold.
    function test_mul_by_zero(SN32x32 a) public {
        assertEq(a.mul(ZERO), ZERO);
    }

    /// @notice `a * 2 = a + a` should hold for `a` in `[MIN/2, MAX/2]`..
    function test_mul_by_two(SN32x32 a) public {
        a = bound(a, MIN_HALF, MAX_HALF);

        assertEq(a.mul(TWO), a.add(a));
    }

    /// @notice `a * (-1) = -a` should hold for `a` in `(MIN, MAX]`.
    function test_mul_by_neg_one(SN32x32 a) public {
        a = bound(a, MAX.neg(), MAX);

        assertEq(a.mul(NEG_ONE), a.neg());
    }

    /// @notice `a * b = b * a` should hold or revert.
    function test_mul_commutative(SN32x32 a, SN32x32 b) public canRevert {
        assertEq(a.mul(b), b.mul(a));
    }

    /// @notice `(a * b) * c = a * (b * c)` should hold or revert.
    function test_mul_associative(SN32x32 a, SN32x32 b, SN32x32 c) public canRevert {
        // Bounding to third root of MAX to prevent overflow rejects.
        a = bound(a, ONE, wrap(1290 << 32));
        b = bound(b, ONE, wrap(1290 << 32));
        c = bound(c, ONE, wrap(1290 << 32));

        // Approximate due to rounding errors.
        // todo: investigate.
        assertApproxEqRel(a.mul(b.mul(c)), a.mul(b).mul(c), 0.000000001e18);
    }

    /// @notice `a * (b + c) = a * b + a * c` should hold or revert.
    function test_mul_distributive(SN32x32 a, SN32x32 b, SN32x32 c) public canRevert {
        // Approximate due to rounding errors.
        assertApproxEqAbs(a.mul(b.add(c)), a.mul(b).add(a.mul(c)), 1);
    }

    /// @notice `a * b` should overflow for `a` in `(0, MAX)`, `b` in `(MAX/a, MAX]`.
    function test_mul_revert_Overflow(SN32x32 a, SN32x32 b) public {
        a = bound(a, ONE.add(wrap(1)), MAX);
        b = bound(b, MAX.divUp(a).add(wrap(1)), MAX);

        vm.expectRevert();

        a.mul(b);
    }

    /* ------------- div ------------- */

    /// @notice `a / 1 = a` should hold.
    function test_div_by_one(SN32x32 a) public {
        assertEq(a.div(ONE), a);
    }

    /// @notice `a / 0` should revert.
    function test_div_by_zero(SN32x32 a) public {
        vm.expectRevert();

        a.div(ZERO);
    }

    /// @notice `(a * 2) / 2 = a` should hold for `a` in `[MIN/2, MAX/2]`.
    function test_div_by_two(SN32x32 a) public {
        a = bound(a, MIN_HALF, MAX_HALF);

        assertEq(a.mul(TWO).div(TWO), a);
    }

    /// @notice `a / (-1) = -a` should hold for `a` in `(MIN, MAX]`.
    function test_div_by_neg_one(SN32x32 a) public {
        a = bound(a, MAX.neg(), MAX);

        assertEq(a.div(NEG_ONE), a.neg());
    }

    /// @notice `(a * b) / b = a` should approx. hold or revert.
    function test_mul_div(SN32x32 a, SN32x32 b) public canRevert {
        assertApproxEqAbs(a.mul(b).div(b), a, ONE);
        assertApproxEqAbs(a.div(b).mul(b), a, ONE);
    }

    /// @notice `(a * b) / b = a` should approx. hold or revert for
    ///         `|a|` in `[ONE, MAX]`, `|a*b|` in `[|a|, MAX]`
    function test_mul_div_precision(SN32x32 a, SN32x32 b) public canRevert {
        a = bound(a.abs(), ONE, MAX).mul(a.sign());
        b = bound(b.abs(), ONE, MAX.div(a.abs())).mul(b.sign());

        assertApproxEqAbs(a.mul(b).div(b), a, 1);
    }

    /// @notice `(a / b) * b = a` should approx. hold or revert for
    ///         `|a|` in `[0, ONE]`, `|b|` in `[|a/MAX|, ONE]`
    function test_div_mul_precision(SN32x32 a, SN32x32 b) public canRevert {
        a = bound(a.abs(), ZERO, ONE).mul(a.sign());
        b = bound(b.abs(), a.abs().div(MAX), ONE).mul(b.sign());

        assertApproxEqAbs(a.div(b).mul(b), a, 1);
    }

    /* ------------- divUp ------------- */

    /// @notice The result of `divUp` should always be greater than or equal to `div`.
    function test_divUp(SN32x32 a, SN32x32 b) public canRevert {
        SN32x32 c = a.div(b);
        SN32x32 d = a.divUp(b);

        assertGte(d, c);
        assertApproxEqAbs(c, d, 2);
    }
}
