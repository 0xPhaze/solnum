// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "src/N32x32.sol";
import "forge-std/Test.sol";

contract TestN32x32 is Test {
    function assertEq(N32x32 a, N32x32 b) internal {
        if (N32x32.unwrap(a) != N32x32.unwrap(b)) {
            emit log("Error: a = b not satisfied [N32x32]");
            emit log_named_int("  Expected", N32x32.unwrap(b));
            emit log_named_int("    Actual", N32x32.unwrap(a));
            fail();
        }
    }

    /// @dev Helper function to bound a N32x32 number.
    function bound(N32x32 x, N32x32 min, N32x32 max) internal view returns (N32x32 result) {
        result = N32x32.wrap(int64(bound(int256(x.unwrap()), int256(min.unwrap()), int256(max.unwrap()))));
    }

    /// @dev Helper function to bound a N32x32 number.
    function bound(N32x32 x, int64 min, N32x32 max) internal view returns (N32x32 result) {
        result = N32x32.wrap(int64(bound(int256(x.unwrap()), int256(min), int256(max.unwrap()))));
    }

    /// @dev Helper function to bound a N32x32 number.
    function bound(N32x32 x, N32x32 min, int64 max) internal view returns (N32x32 result) {
        result = N32x32.wrap(int64(bound(int256(x.unwrap()), int256(min.unwrap()), int256(max))));
    }

    /// @dev Helper function to bound a N32x32 number.
    function bound(N32x32 x, int64 min, int64 max) internal view returns (N32x32 result) {
        result = N32x32.wrap(int64(bound(int256(x.unwrap()), int256(min), int256(max))));
    }

    function assertApproxEqAbs(N32x32 a, N32x32 b, N32x32 maxDelta, string memory err) internal virtual {
        assertApproxEqAbs(a.unwrap(), b.unwrap(), uint256(int256(maxDelta.unwrap())), err);
    }

    function assertApproxEqAbs(N32x32 a, N32x32 b, N32x32 maxDelta) internal virtual {
        assertApproxEqAbs(a.unwrap(), b.unwrap(), uint256(int256(maxDelta.unwrap())));
    }

    function assertApproxEqAbs(N32x32 a, N32x32 b, uint256 maxDelta, string memory err) internal virtual {
        assertApproxEqAbs(a.unwrap(), b.unwrap(), maxDelta, err);
    }

    function assertApproxEqAbs(N32x32 a, N32x32 b, uint256 maxDelta) internal virtual {
        assertApproxEqAbs(a.unwrap(), b.unwrap(), maxDelta);
    }

    /* ------------- log ------------- */

    function logN(N32x32 a) public {
        logN("", a);
    }

    function logN(string memory name, N32x32 a) public {
        int64 uInt64;
        int256 uInt256;
        bytes32 uBytes;
        assembly {
            uBytes := a
            uInt64 := a
            uInt256 := a
        }
        emit log(name);
        emit log_int(uInt64);
        emit log_int(uInt256 >> 32);
        emit log_int((uInt256 & 0xffffffff) << 32);
        emit log_bytes32(uBytes);
    }

    // function test_log() public {
    //     // logN("ONE", ONE);
    //     logN("-ONE", ONE.neg());
    //     console.log();
    //     // logN("HALF", HALF);
    //     // console.log();
    //     // logN("TENTH", ONE.div(10));
    //     // emit log_named_int('MIN:', N32x32.)
    // }

    modifier canRevert() {
        if (msg.sender == address(this)) {
            _;
        } else {
            (bool success,) = address(this).call(msg.data);

            vm.assume(success);
        }
    }

    /* ------------- add ------------- */

    function test_add(N32x32 a) public {
        assertEq(a.add(ZERO), a);
    }

    function test_add_revert_Overflow() public {
        vm.expectRevert();

        MAX_HALF.add(MAX_HALF).add(wrap(2));
    }

    function test_add_revert_Overflow(N32x32 a, N32x32 b) public {
        a = bound(a, MIN_HALF.neg(), MAX);
        b = bound(b, MIN_HALF.neg(), MAX);

        vm.expectRevert();

        a.add(b).add(wrap(1));
    }

    function test_add_revert_Underflow(N32x32 a, N32x32 b) public {
        a = bound(a, MIN, MIN_HALF);
        b = bound(b, MIN, MIN_HALF);

        vm.expectRevert();

        a.add(b).add(wrap(-1));
    }

    function test_add_commutative(N32x32 a, N32x32 b) public {
        a = bound(a, MIN_HALF, MAX_HALF);
        b = bound(b, MIN_HALF, MAX_HALF);

        // a + b = b + a
        assertEq(a.add(b), b.add(a));
    }

    function test_add_commutative_r(N32x32 a, N32x32 b) public canRevert {
        // a + b = b + a
        assertEq(a.add(b), b.add(a));
    }

    function test_add_associative_r(N32x32 a, N32x32 b, N32x32 c) public canRevert {
        // (a + b) + c = a + (b + c)
        assertEq(a.add(b).add(c), a.add(b.add(c)));
    }

    /* ------------- sub ------------- */

    function test_sub(N32x32 a, N32x32 b) public {
        a = bound(a, MIN_HALF, MAX_HALF);
        b = bound(b, MIN_HALF, MAX_HALF);

        // a - b = a + (-b)
        assertEq(a.sub(b), a.add(ZERO.sub(b)));
    }

    function test_sub_r(N32x32 a, N32x32 b) public canRevert {
        // a - b = a + (-b)
        assertEq(a.sub(b), a.add(ZERO.sub(b)));
    }

    function test_sub_property(N32x32 a, N32x32 b) public {
        a = bound(a, MIN_HALF, MAX_HALF);
        b = bound(b, MIN_HALF, MAX_HALF);

        // a - b = -(b - a)
        assertEq(a.sub(b), ZERO.sub(b.sub(a)));
    }

    function test_sub_property_r(N32x32 a, N32x32 b) public canRevert {
        // a - b = -(b - a)
        assertEq(a.sub(b), ZERO.sub(b.sub(a)));
    }

    function test_sub_revert_Overflow(N32x32 a, N32x32 b) public {
        a = bound(a, MAX_HALF, MAX);
        b = bound(b, MIN, MIN_HALF);

        vm.expectRevert();

        a.sub(b).sub(wrap(-1));
    }

    function test_sub_revert_Underflow() public {
        vm.expectRevert();

        MIN_HALF.sub(MAX_HALF).sub(wrap(2));
    }

    function test_sub_revert_Underflow(N32x32 a, N32x32 b) public {
        a = bound(a, MIN, MIN_HALF);
        b = bound(b, MIN_HALF.neg(), MAX);

        vm.expectRevert();

        a.sub(b).sub(wrap(1));
    }

    /* ------------- add & sub ------------- */

    function test_add_sub(N32x32 a, N32x32 b) public {
        a = bound(a, MIN_HALF, MAX_HALF);
        b = bound(b, MIN_HALF, MAX_HALF);

        // (a + b) - b = a
        assertEq(a.add(b).sub(b), a);
        // (a - b) + b = a
        assertEq(a.sub(b).add(b), a);
    }

    function test_add_sub_r(N32x32 a, N32x32 b) public canRevert {
        // (a + b) - b = a
        assertEq(a.add(b).sub(b), a);
    }

    function test_sub_add_r(N32x32 a, N32x32 b) public canRevert {
        // (a - b) + b = a
        assertEq(a.sub(b).add(b), a);
    }

    /* ------------- neg ------------- */

    function test_neg_revert_Overflow() public {
        vm.expectRevert();

        MIN.neg();
    }

    function test_neg(N32x32 a) public {
        a = bound(a, MAX.neg(), MAX);

        // -a = 0 - a
        assertEq(a.neg(), ZERO.sub(a));
    }

    /* ------------- sign ------------- */

    function test_sign(N32x32 a) public {
        a = bound(a, ZERO, MAX);

        // sign(a) = 1
        assertEq(a.sign(), ONE);
    }

    function test_sign_neg(N32x32 a) public {
        a = bound(a, MIN, ZERO.sub(wrap(1)));

        // sign(a) = -1
        assertEq(a.sign(), NEG_ONE);
    }

    /* ------------- abs ------------- */

    function test_abs(N32x32 a) public {
        a = bound(a, ZERO, MAX);

        // |a| = a
        assertEq(a.abs(), a);
    }

    function test_abs_neg(N32x32 a) public {
        a = bound(a, MAX.neg(), ZERO);

        // |a| = -a
        assertEq(a.abs(), a.neg());
    }

    function test_abs_revert_Overflow() public {
        vm.expectRevert();

        MIN.abs();
    }

    /* ------------- mul ------------- */

    function test_mul_by_one(N32x32 a) public {
        // a * 1 = a
        assertEq(a.mul(ONE), a);
    }

    function test_mul_by_zero(N32x32 a) public {
        assertEq(a.mul(ZERO), ZERO);
    }

    function test_mul_by_two(N32x32 a) public {
        a = bound(a, MIN_HALF, MAX_HALF);

        // a * 2 = a + a
        assertEq(a.mul(TWO), a.add(a));
    }

    function test_mul_by_neg_one(N32x32 a) public {
        a = bound(a, MAX.neg(), MAX);

        // a * (-1) = -a
        assertEq(a.mul(NEG_ONE), a.neg());
        // (a * (-1)) * (-1) = a
        assertEq(a.mul(NEG_ONE).mul(NEG_ONE), a);
    }

    function test_mul_commutative(N32x32 a, N32x32 b) public canRevert {
        // a * b = b * a
        assertEq(a.mul(b), b.mul(a));
    }

    function test_mul_distributive(N32x32 a, N32x32 b, N32x32 c) public canRevert {
        // a * (b + c) = a * b + a * c
        // Approximate due to rounding errors.
        assertApproxEqAbs(a.mul(b.add(c)), a.mul(b).add(a.mul(c)), 1);
    }

    function test_mul_revert_Overflow(N32x32 a) public {
        // `MAX * [ONE + 1, MAX)` should overflow.
        a = bound(a, ONE.add(wrap(1)), MAX);

        vm.expectRevert();

        MAX.mul(a);
    }

    /* ------------- div ------------- */

    function test_div_by_one(N32x32 a) public {
        // a / 1 = a
        assertEq(a.div(ONE), a);
    }

    function test_div_by_zero(N32x32 a) public {
        vm.expectRevert();

        a.div(ZERO);
    }

    function test_div_by_two(N32x32 a) public {
        a = bound(a, MIN_HALF, MAX_HALF);

        // (a * 2) / 2 = a
        assertEq(a.mul(TWO).div(TWO), a);
    }

    function test_div_by_neg_one(N32x32 a) public {
        a = bound(a, MAX.neg(), MAX);

        // a / (-1) = -a
        assertEq(a.div(NEG_ONE), a.neg());
        // (a / (-1)) / (-1) = a
        assertEq(a.div(NEG_ONE).div(NEG_ONE), a);
    }

    function test_mul_div(N32x32 a, N32x32 b) public canRevert {
        // (a * b) / b ≈ a
        assertApproxEqAbs(a.mul(b).div(b), a, ONE);
        // (a / b) * b ≈ a
        assertApproxEqAbs(a.div(b).mul(b), a, ONE);
    }

    function test_mul_div_precision(N32x32 a, N32x32 b) public canRevert {
        a = bound(a.abs(), ONE, MAX).mul(a.sign());
        b = bound(b.abs(), ONE, MAX.div(a.abs())).mul(b.sign());

        // (a * b) / b ≈ a
        assertApproxEqAbs(a.mul(b).div(b), a, 1);
    }

    function test_div_mul_precision(N32x32 a, N32x32 b) public canRevert {
        a = bound(a.abs(), ZERO, ONE).mul(a.sign());
        b = bound(b.abs(), a.abs().div(MAX), ONE).mul(b.sign());

        // (a / b) * b ≈ a
        assertApproxEqAbs(a.div(b).mul(b), a, 1);
    }
}
