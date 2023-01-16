// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {N32x32, UINT64_MAX} from "src/N32x32.sol";
import {M32x32} from "src/M32x32.sol";
import {UM256} from "src/UM256.sol";

import "forge-std/Test.sol";

contract TestHelper is Test {
    /* ------------- N32x32 ------------- */

    function assertEq(N32x32 a, N32x32 b) internal {
        if (N32x32.unwrap(a) != N32x32.unwrap(b)) {
            emit log("Error: a = b not satisfied [N32x32]");
            emit log_named_int("  Expected", N32x32.unwrap(b));
            emit log_named_int("    Actual", N32x32.unwrap(a));
            fail();
        }
    }

    function assertGte(N32x32 a, N32x32 b) internal {
        if (N32x32.unwrap(a) < N32x32.unwrap(b)) {
            emit log("Error: a >= b not satisfied [N32x32]");
            emit log_named_int("  Value a", N32x32.unwrap(b));
            emit log_named_int("  Value b", N32x32.unwrap(a));
            fail();
        }
    }

    function assertGt(N32x32 a, N32x32 b) internal {
        if (N32x32.unwrap(a) <= N32x32.unwrap(b)) {
            emit log("Error: a > b not satisfied [N32x32]");
            emit log_named_int("  Value a", N32x32.unwrap(b));
            emit log_named_int("  Value b", N32x32.unwrap(a));
            fail();
        }
    }

    function bound(N32x32 x, N32x32 min, N32x32 max) internal view returns (N32x32 result) {
        result = N32x32.wrap(int64(bound(int256(x.unwrap()), int256(min.unwrap()), int256(max.unwrap()))));
    }

    function bound(N32x32 x, int64 min, N32x32 max) internal view returns (N32x32 result) {
        result = N32x32.wrap(int64(bound(int256(x.unwrap()), int256(min), int256(max.unwrap()))));
    }

    function bound(N32x32 x, N32x32 min, int64 max) internal view returns (N32x32 result) {
        result = N32x32.wrap(int64(bound(int256(x.unwrap()), int256(min.unwrap()), int256(max))));
    }

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

    function assertApproxEqRel(N32x32 a, N32x32 b, uint256 maxPercentDelta) internal virtual {
        assertApproxEqRel(a.unwrap(), b.unwrap(), maxPercentDelta);
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

    /* ------------- UM256 ------------- */

    function assertEq(UM256 A, uint256 s) internal {
        if (!A.eqScalar(s)) {
            emit log("Error: A == B not satisfied [UM256]");
            emit log_named_uint("  Expected", s);
            emit log("    Actual");
            logMat(A);
            fail();
        }
    }

    function assertEq(UM256 A, UM256 B) internal {
        if (!A.eq(B)) {
            emit log("Error: A == B not satisfied [UM256]");
            emit log("  Expected");
            logMat(B);
            emit log("    Actual");
            logMat(A);
            fail();
        }
    }

    function assertNEq(UM256 A, UM256 B) internal {
        if (A.eq(B)) {
            emit log("Error: A != B not satisfied [UM256]");
            logMat(B);
            fail();
        }
    }

    function assertIsEye(UM256 A) internal {
        (uint256 n, uint256 m) = A.shape();

        for (uint256 i; i < n; ++i) {
            for (uint256 j; j < m; ++j) {
                assertEq(A.at(i, j), (i == j) ? 1 : 0);
            }
        }
    }

    /* ------------- M32x32 ------------- */

    function assertEq(M32x32 A, uint256 v) internal {
        if (!A.eqScalar(v)) {
            emit log("Error: A == b not satisfied [M32x32]");
            emit log_named_uint("  Expected", v);
            emit log("    Actual");
            logMat(A);
            fail();
        }
    }

    function assertEq(M32x32 A, M32x32 B) internal {
        if (!A.eq(B)) {
            emit log("Error: A == B not satisfied [M32x32]");
            emit log("  Expected");
            logMat(B);
            emit log("    Actual");
            logMat(A);
            fail();
        }
    }

    function assertNEq(M32x32 A, M32x32 B) internal {
        if (A.eq(B)) {
            emit log("Error: A != B not satisfied [M32x32]");
            logMat(B);
            fail();
        }
    }

    function assertIsEye(M32x32 A) internal {
        (uint256 n, uint256 m) = A.shape();

        for (uint256 i; i < n; ++i) {
            for (uint256 j; j < m; ++j) {
                assertEq(A.at(i, j), (i == j) ? 1 : 0);
            }
        }
    }

    function setFreeMemPtr(uint256 loc) internal pure {
        assembly {
            mstore(0x40, loc)
        }
    }

    function freeMemPtr() internal pure returns (uint256 memPtr) {
        assembly {
            memPtr := mload(0x40)
        }
    }

    bytes32 constant _MAGIC_VALUE = 0x2bdba7ddf640d8dba63497f8f2088af9fa01709eb45d239463a00082e9ccf36f;

    function storeMagicValueAt(uint256 loc) internal pure {
        assembly {
            mstore(loc, _MAGIC_VALUE)
        }
    }

    function mload(uint256 loc) internal pure returns (bytes32 value) {
        assembly {
            value := mload(loc)
        }
    }

    function assertMagicValueAt(uint256 loc) internal {
        bytes32 value;

        assembly {
            value := mload(loc)
        }

        assertEq(value, _MAGIC_VALUE, "Magic Value not found");
    }

    function appendDirtyBits(M32x32 A) internal pure {
        uint256 len = A.length();
        uint256 lenUp = ((len * 8 + 31) & ~uint256(31)) / 8;

        while (lenUp != len) {
            A.setUnsafe(0, lenUp - 1, UINT64_MAX);

            lenUp -= 1;
        }
    }

    /* ------------- log ------------- */

    function lognewHeader(M32x32 A) internal view {
        bytes32 data;
        assembly {
            data := mload(A)
        }
        console.logBytes32(data);
    }

    function logMat(UM256 A) internal {
        (uint256 n, uint256 m) = A.shape();

        string memory str = string.concat("\nUM256(", vm.toString(n), ",", vm.toString(m), "):\n");

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

    function logMat(M32x32 A) internal {
        (uint256 n, uint256 m) = A.shape();

        string memory str = string.concat("\nM32x32(", vm.toString(n), ",", vm.toString(m), "):\n");

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

    // function logMem(M32x32 A) public {
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

    function mdump(uint256 location) internal view {
        mdump(location, 1);
    }

    function mdump(uint256 location, uint256 numSlots) internal view {
        bytes32 m;

        for (uint256 i; i < numSlots; i++) {
            assembly {
                m := mload(add(location, mul(0x20, i)))
            }

            console.log(
                string.concat(vm.toString(abi.encodePacked(bytes2(uint16(location + 0x20 * i)))), ": ", vm.toString(m))
            );
        }

        console.log();
    }
}
