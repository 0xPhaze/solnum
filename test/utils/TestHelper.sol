// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {N32x32, UINT64_MASK, ZERO, ONE} from "src/N32x32.sol";
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

    address private constant canRevertCaller = 0xc65f435F6dC164bE5D52Bc0a90D9A680052bFab2;

    modifier canRevert() {
        if (msg.sender == canRevertCaller) {
            _;
        } else {
            vm.prank(canRevertCaller);

            (bool success, bytes memory returndata) = address(this).call(msg.data);

            if (success) {
                assembly {
                    return(add(returndata, 32), mload(returndata))
                }
            } else {
                vm.assume(false);
            }
        }
    }

    modifier canRevertWithMsg(string memory message) {
        if (msg.sender == canRevertCaller) {
            _;
        } else {
            vm.prank(canRevertCaller);

            (bool success, bytes memory returndata) = address(this).call(msg.data);

            if (success) {
                assembly {
                    return(add(returndata, 32), mload(returndata))
                }
            } else {
                assertTrue(returndata.length >= 4 + 32, "Call did not revert as expected");

                string memory revertMsg;

                assembly {
                    revertMsg := add(returndata, 68)
                }

                assertEq(revertMsg, message, "Call did not revert as expected");

                vm.assume(false);
            }
        }
    }

    modifier canRevertWithSelector(bytes4 selector) {
        if (msg.sender == canRevertCaller) {
            _;
        } else {
            vm.prank(canRevertCaller);

            (bool success, bytes memory returndata) = address(this).call(msg.data);

            if (success) {
                assembly {
                    return(add(returndata, 32), mload(returndata))
                }
            } else {
                assertEq(bytes4(returndata), selector, "Call did not revert as expected");

                vm.assume(false);
            }
        }
    }

    function assertEqCall(bytes memory calldata1, bytes memory calldata2) internal {
        assertEqCall(address(this), calldata1, address(this), calldata2, true);
    }

    function assertEqCall(bytes memory calldata1, bytes memory calldata2, bool requireEqualRevertData) internal {
        assertEqCall(address(this), calldata1, address(this), calldata2, requireEqualRevertData);
    }

    function assertEqCall(address addr, bytes memory calldata1, bytes memory calldata2) internal {
        assertEqCall(addr, calldata1, addr, calldata2, true);
    }

    function assertEqCall(address addr, bytes memory calldata1, bytes memory calldata2, bool requireEqualRevertData)
        internal
    {
        assertEqCall(addr, calldata1, addr, calldata2, requireEqualRevertData);
    }

    function assertEqCall(address address1, bytes memory calldata1, address address2, bytes memory calldata2)
        internal
    {
        assertEqCall(address1, calldata1, address2, calldata2, true);
    }

    function assertEqCall(
        address address1,
        bytes memory calldata1,
        address address2,
        bytes memory calldata2,
        bool requireEqualRevertData
    ) internal {
        (bool success1, bytes memory returndata1) = address(address1).call(calldata1);
        (bool success2, bytes memory returndata2) = address(address2).call(calldata2);

        if (success1 && success2) {
            if (keccak256(returndata1) == keccak256(returndata2)) {
                emit log_named_bytes("Both calls returned", returndata1);
            } else {
                assertEq(returndata1, returndata2, "Returned value does not match");
            }
        }
        if (!success1 && success2) {
            emit log("Error: Call reverted unexpectedly");
            emit log_named_bytes("  Expected return-value", returndata2);
            emit log_named_bytes("       Call revert-data", returndata1);
            fail();
        }
        if (success1 && !success2) {
            emit log("Error: Call did not revert");
            emit log_named_bytes("  Expected revert-data", returndata2);
            emit log_named_bytes("     Call return-value", returndata1);
            fail();
        }
        if (!success1 && !success2 && requireEqualRevertData) {
            assertEq(returndata1, returndata2, "Call revert data does not match");
        }
        if (!success1 && !success2) {
            if (keccak256(returndata1) == keccak256(returndata2)) {
                emit log_named_bytes("Both call revert-data", returndata1);
            } else {
                emit log_named_bytes(" First call revert-data", returndata1);
                emit log_named_bytes("Second call revert-data", returndata2);
            }
        }
    }
    /* ------------- UM256 ------------- */

    function assertEq(UM256 A, uint256 s) internal {
        if (!A.eqAllScalar(s)) {
            emit log("Error: A == s not satisfied [UM256]");
            emit log_named_uint("  Expected", s);
            emit log("    Actual:");
            logMat(A);
            fail();
        }
    }

    function assertLt(UM256 A, uint256 s) internal {
        if (!A.ltAllScalar(s)) {
            emit log("Error: A < s not satisfied [UM256]");
            emit log_named_uint("  Expected", s);
            emit log("    Actual:");
            logMat(A);
            fail();
        }
    }

    function assertGt(UM256 A, uint256 s) internal {
        if (!A.ltAllScalar(s)) {
            emit log("Error: A > s not satisfied [UM256]");
            emit log_named_uint("  Expected", s);
            emit log("    Actual:");
            logMat(A);
            fail();
        }
    }

    function assertEq(UM256 A, UM256 B) internal {
        if (!A.eqAll(B)) {
            emit log("Error: A == B not satisfied [UM256]");
            emit log("  Expected:");
            logMat(B);
            emit log("    Actual:");
            logMat(A);
            fail();
        }
    }

    function assertNEq(UM256 A, UM256 B) internal {
        if (A.eqAll(B)) {
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

    function assertLt(M32x32 A, uint256 s) internal {
        if (!A.ltAllScalar(s)) {
            emit log("Error: A < s not satisfied [M32x32]");
            emit log_named_uint("  Expected", s);
            emit log("    Actual:");
            logMat(A);
            fail();
        }
    }

    function assertGt(M32x32 A, uint256 s) internal {
        // if (!A.gtAllScalar(N32x32.wrap(int64(int256(s))))) {
        if (!A.gtAllScalar(s)) {
            emit log("Error: A > s not satisfied [M32x32]");
            emit log_named_uint("  Expected", s);
            emit log("    Actual:");
            logMat(A);
            fail();
        }
    }

    function assertEq(M32x32 A, uint256 s) internal {
        if (!A.eqAllScalar(N32x32.wrap(int64(int256(s))))) {
            emit log("Error: A == s not satisfied [M32x32]");
            emit log_named_uint("  Expected", s);
            emit log("    Actual:");
            logMat(A);
            fail();
        }
    }

    // function assertLt(M32x32 A, N32x32 s) internal {
    //     if (!A.ltAllScalar(s)) {
    //         emit log("Error: A < s not satisfied [M32x32]");
    //         emit log_named_uint("  Expected", s);
    //         emit log("    Actual:");
    //         logMat(A);
    //         fail();
    //     }
    // }

    // function assertGt(M32x32 A, N32x32 s) internal {
    //     if (!A.gtAllScalar(s)) {
    //         emit log("Error: A > s not satisfied [M32x32]");
    //         emit log_named_uint("  Expected", s);
    //         emit log("    Actual:");
    //         logMat(A);
    //         fail();
    //     }
    // }

    function assertEq(M32x32 A, N32x32 s) internal {
        if (!A.eqAllScalar(s)) {
            emit log("Error: A == s not satisfied [M32x32]");
            logNum("  Expected", s);
            emit log("    Actual:");
            logMat(A);
            fail();
        }
    }

    function assertEq(M32x32 A, M32x32 B) internal {
        if (!A.eqAll(B)) {
            emit log("Error: A == B not satisfied [M32x32]");
            emit log("  Expected:");
            logMat(B);
            emit log("    Actual:");
            logMat(A);
            fail();
        }
    }

    function assertNEq(M32x32 A, M32x32 B) internal {
        if (A.eqAll(B)) {
            emit log("Error: A != B not satisfied [M32x32]");
            logMat(B);
            fail();
        }
    }

    function assertIsEye(M32x32 A) internal {
        (uint256 n, uint256 m) = A.shape();

        for (uint256 i; i < n; ++i) {
            for (uint256 j; j < m; ++j) {
                assertEq(A.at(i, j), (i == j) ? ONE : ZERO);
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

    function appendMagicValue(M32x32 A) internal pure returns (uint256) {
        uint256 memPtr = freeMemPtr();
        uint256 sizeUp = (A.length() * 8 + 31) & ~uint256(31);

        require(memPtr == A.ref() + sizeUp, "Can't append Magic value.");

        assembly {
            mstore(memPtr, _MAGIC_VALUE)
            mstore(0x40, add(0x20, memPtr))
        }

        return memPtr;
    }

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

    function assertMagicValueAt(M32x32 A) internal {
        uint256 sizeUp = (A.length() * 8 + 31) & ~uint256(31);
        uint256 loc = A.ref() + sizeUp;
        bytes32 value;

        assembly {
            value := mload(loc)
        }

        assertEq(value, _MAGIC_VALUE, "Magic value not found");
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
            A.setUnsafe(0, lenUp - 1, N32x32.wrap(int64(uint64(UINT64_MASK))));

            lenUp -= 1;
        }
    }

    /* ------------- log ------------- */

    function logInt(string memory name, int256 x) internal view {
        if (x == type(int256).min) {
            console2.log(name, "57896044618658097711785492504343953926634992332820282019728792003956564819968");
        } else {
            console2.log(name, string.concat(x >= 0 ? "" : "-", vm.toString(x > 0 ? x : -x)));
        }
    }

    function logHeader(M32x32 A) internal view {
        bytes32 data;
        assembly {
            data := mload(A)
        }
        console.logBytes32(data);
    }

    function logNum(N32x32 a) internal {
        logNum("N32x32", a, 2);
    }

    function logNum(string memory name, N32x32 a) internal {
        logNum(name, a, 2);
    }

    function logNum(N32x32 a, uint256 decimals) internal {
        logNum("N32x32", a, decimals);
    }

    function logNum(string memory name, N32x32 a, uint256 decimals) internal {
        string memory repr = toString(a, decimals);

        if (bytes(name).length != 0) repr = string.concat(name, ": ", repr);

        emit log(repr);
    }

    function toString(N32x32 a, uint256 decimals) internal pure returns (string memory repr) {
        int256 ua = int64(N32x32.unwrap(a));
        bool sign = ua < 0;
        uint256 abs = uint256(sign ? -ua : ua);
        uint256 upper = abs >> 32;
        uint256 lower = (uint256(uint32(abs)) * (10 ** decimals) + (1 << 31)) >> 32;

        repr = string.concat(sign ? "-" : "", vm.toString(upper), ".", vm.toString(lower));
    }

    function logMat(UM256 A) internal {
        logMat("", A);
    }

    function logMat(string memory name, UM256 A) internal {
        (uint256 n, uint256 m) = A.shape();

        string memory repr = string.concat("\nUM256(", vm.toString(n), ",", vm.toString(m), "): ", name, "\n");

        uint256 max = 10;

        for (uint256 i; i < n && i < max; ++i) {
            for (uint256 j; j < m && j < max; ++j) {
                if (i == max - 1) repr = string.concat(repr, "..\t");
                else if (j == max - 1) repr = string.concat(repr, "..");
                else repr = string.concat(repr, string.concat(vm.toString(A.at(i, j)), " \t"));
            }
            repr = string.concat(repr, "\n");
        }

        emit log(repr);
    }

    function logMat(M32x32 A) internal {
        logMat("", A, 2);
    }

    function logMat(M32x32 A, uint256 decimals) internal {
        logMat("", A, decimals);
    }

    function logMat(string memory name, M32x32 A, uint256 decimals) internal {
        (uint256 n, uint256 m) = A.shape();

        string memory repr = string.concat("\nM32x32(", vm.toString(n), ",", vm.toString(m), "): ", name, "\n");

        uint256 max = 10;

        for (uint256 i; i < n && i < max; ++i) {
            for (uint256 j; j < m && j < max; ++j) {
                if (i == max - 1) {
                    repr = string.concat(repr, "..\t");
                } else if (j == max - 1) {
                    repr = string.concat(repr, "..");
                } else {
                    repr = string.concat(repr, string.concat(toString(A.at(i, j), decimals), " \t"));
                }
            }
            repr = string.concat(repr, "\n");
        }

        emit log(repr);
    }

    // function logMem(M32x32 A) public {
    //     // (uint256 n, uint256 m) = A.shape();
    //     (uint256 n, uint256 m, uint256 data, uint256 size) = A.header();

    //     string memory repr = string.concat("\nMem(", vm.toString(n), ",", vm.toString(m), "):\n");

    //     for (uint256 i; i < n; ++i) {
    //         for (uint256 j; j < m; ++j) {
    //             uint256 el;
    //             assembly {
    //                 el := mload(add(data, mul(add(mul(i, m), j), size)))
    //             }
    //             repr = string.concat(repr, string.concat(vm.toString(el), "\t"));
    //         }
    //         repr = string.concat(repr, "\n");
    //     }

    //     emit log(repr);

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
