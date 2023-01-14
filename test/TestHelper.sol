// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "src/SN32x32.sol";
import "src/SM32x32.sol";

import "forge-std/Test.sol";

using SM32x32Lib for SM32x32;

contract TestHelper is Test {
    /* ------------- SN32x32 ------------- */

    function assertEq(SN32x32 a, SN32x32 b) internal {
        if (SN32x32.unwrap(a) != SN32x32.unwrap(b)) {
            emit log("Error: a = b not satisfied [SN32x32]");
            emit log_named_int("  Expected", SN32x32.unwrap(b));
            emit log_named_int("    Actual", SN32x32.unwrap(a));
            fail();
        }
    }

    function assertGte(SN32x32 a, SN32x32 b) internal {
        if (SN32x32.unwrap(a) < SN32x32.unwrap(b)) {
            emit log("Error: a >= b not satisfied [SN32x32]");
            emit log_named_int("  Value a", SN32x32.unwrap(b));
            emit log_named_int("  Value b", SN32x32.unwrap(a));
            fail();
        }
    }

    function assertGt(SN32x32 a, SN32x32 b) internal {
        if (SN32x32.unwrap(a) <= SN32x32.unwrap(b)) {
            emit log("Error: a > b not satisfied [SN32x32]");
            emit log_named_int("  Value a", SN32x32.unwrap(b));
            emit log_named_int("  Value b", SN32x32.unwrap(a));
            fail();
        }
    }

    function bound(SN32x32 x, SN32x32 min, SN32x32 max) internal view returns (SN32x32 result) {
        result = SN32x32.wrap(int64(bound(int256(x.unwrap()), int256(min.unwrap()), int256(max.unwrap()))));
    }

    function bound(SN32x32 x, int64 min, SN32x32 max) internal view returns (SN32x32 result) {
        result = SN32x32.wrap(int64(bound(int256(x.unwrap()), int256(min), int256(max.unwrap()))));
    }

    function bound(SN32x32 x, SN32x32 min, int64 max) internal view returns (SN32x32 result) {
        result = SN32x32.wrap(int64(bound(int256(x.unwrap()), int256(min.unwrap()), int256(max))));
    }

    function bound(SN32x32 x, int64 min, int64 max) internal view returns (SN32x32 result) {
        result = SN32x32.wrap(int64(bound(int256(x.unwrap()), int256(min), int256(max))));
    }

    function assertApproxEqAbs(SN32x32 a, SN32x32 b, SN32x32 maxDelta, string memory err) internal virtual {
        assertApproxEqAbs(a.unwrap(), b.unwrap(), uint256(int256(maxDelta.unwrap())), err);
    }

    function assertApproxEqAbs(SN32x32 a, SN32x32 b, SN32x32 maxDelta) internal virtual {
        assertApproxEqAbs(a.unwrap(), b.unwrap(), uint256(int256(maxDelta.unwrap())));
    }

    function assertApproxEqAbs(SN32x32 a, SN32x32 b, uint256 maxDelta, string memory err) internal virtual {
        assertApproxEqAbs(a.unwrap(), b.unwrap(), maxDelta, err);
    }

    function assertApproxEqAbs(SN32x32 a, SN32x32 b, uint256 maxDelta) internal virtual {
        assertApproxEqAbs(a.unwrap(), b.unwrap(), maxDelta);
    }

    function assertApproxEqRel(SN32x32 a, SN32x32 b, uint256 maxPercentDelta) internal virtual {
        assertApproxEqRel(a.unwrap(), b.unwrap(), maxPercentDelta);
    }

    /* ------------- log ------------- */

    function logN(SN32x32 a) public {
        logN("", a);
    }

    function logN(string memory name, SN32x32 a) public {
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
    //     // emit log_named_int('MIN:', SN32x32.)
    // }

    modifier canRevert() {
        if (msg.sender == address(this)) {
            _;
        } else {
            (bool success, bytes memory returndata) = address(this).call(msg.data);

            if (!success) {
                // if (returndata.length != 4 || bytes4(returndata) != selector) {
                //     emit log("Call did not revert as expected");
                //     emit log_named_bytes("  Expected", abi.encodePacked(selector));
                //     emit log_named_bytes("    Actual", returndata);
                //     fail();
                // } else {}
                vm.assume(false);
            }
        }
    }

    /* ------------- SM32x32 ------------- */

    function assertEq(SM32x32 a, uint256 v) internal {
        if (!a.eq(v)) {
            emit log("Error: a == b not satisfied [SM32x32]");
            emit log_named_uint("  Expected", v);
            emit log("    Actual");
            logMat(a);
            fail();
        }
    }

    function assertEq(SM32x32 a, SM32x32 b) internal {
        if (!a.eq(b)) {
            emit log("Error: a == b not satisfied [SM32x32]");
            emit log("  Expected");
            logMat(b);
            emit log("    Actual");
            logMat(a);
            fail();
        }
    }

    function assertNEq(SM32x32 a, SM32x32 b) internal {
        if (a.eq(b)) {
            emit log("Error: a != b not satisfied [SM32x32]");
            logMat(b);
            fail();
        }
    }

    function assertIsEye(SM32x32 A) internal {
        (uint256 n, uint256 m) = A.shape();

        for (uint256 i; i < n; ++i) {
            for (uint256 j; j < m; ++j) {
                assertEq(A.at(i, j), (i == j) ? 1 : 0);
            }
        }
    }

    function freeMemPtr() internal pure returns (uint256 memPtr) {
        assembly {
            memPtr := mload(0x40)
        }
    }

    /* ------------- log ------------- */

    function lognewHeader(SM32x32 A) internal view {
        bytes32 data;
        assembly {
            data := mload(A)
        }
        console.logBytes32(data);
    }

    function logMat(SM32x32 A) public {
        (uint256 n, uint256 m) = A.shape();

        string memory str = string.concat("\nMat(", vm.toString(n), ",", vm.toString(m), "):\n");

        uint256 max = 10;

        for (uint256 i; i < n && i < max; ++i) {
            for (uint256 j; j < m && j < max; ++j) {
                if (i == max - 1) str = string.concat(str, "..\t");
                else str = string.concat(str, string.concat(vm.toString(A.at(i, j)), " \t"));
                if (j == max - 1) str = string.concat(str, "..");
            }
            str = string.concat(str, "\n");
        }

        emit log(str);
    }

    function logMat(uint256[3][3] memory A) public {
        (uint256 n, uint256 m) = (A.length, A[0].length);

        string memory str = string.concat("\nMat(", vm.toString(n), ",", vm.toString(m), "):\n");

        for (uint256 i; i < n; ++i) {
            for (uint256 j; j < m; ++j) {
                str = string.concat(str, string.concat(vm.toString(A[i][j]), "\t"));
            }
            str = string.concat(str, "\n");
        }

        emit log(str);
    }

    // function logMem(SM32x32 A) public {
    //     // (uint256 n, uint256 m) = A.shape();
    //     (uint256 n, uint256 m, uint256 data, uint256 size) = A.header();

    //     string memory str = string.concat("\nMem(", vm.toString(n), ",", vm.toString(m), "):\n");

    //     for (uint256 i; i < n; ++i) {
    //         for (uint256 j; j < m; ++j) {
    //             uint256 el;
    //             assembly {
    //                 el := mload(add(data, mul(add(mul(i, m), j), size)))
    //             }
    //             str = string.concat(str, string.concat(vm.toString(el), "\t"));
    //         }
    //         str = string.concat(str, "\n");
    //     }

    //     emit log(str);

    function mdump(uint256 location, uint256 numSlots) internal view {
        bytes32 m;
        for (uint256 i; i < numSlots; i++) {
            assembly {
                m := mload(add(location, mul(0x20, i)))
            }
            console.logBytes2(bytes2(uint16(location + 0x20 * i)));
            console.logBytes32(m);
        }
        console.log();
    }
}
