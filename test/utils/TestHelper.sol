// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import { N32x32, N32x32Lib } from "src/N32x32.sol";
import { M32x32, M32x32Lib } from "src/M32x32.sol";
import { UM256 } from "src/UM256.sol";

import "forge-std/Test.sol";

interface VmMemSafe is Vm {
    // Only allows memory writes to offsets [0x00, 0x60) ∪ [_min, _max) in the current subcontext. If any other
    // memory is written to, the test will fail.
    function expectSafeMemory(uint64 _min, uint64 _max) external;

    // Only allows memory writes to offsets [0x00, 0x60) ∪ [_min, _max) in the next created subcontext.
    // If any other memory is written to, the test will fail.
    function expectSafeMemoryCall(uint64 _min, uint64 _max) external;
}

contract TestHelper is Test {
    VmMemSafe vm2 = VmMemSafe(address(vm));

    bool log_mat_extended = false;
    uint256 log_mat_max = 10;
    uint256 log_mat_decimals = 2;

    function expectSafeMemoryIncrease(uint256 size) internal {
        uint256 memPtr = freeMemPtr();

        vm2.expectSafeMemory(uint64(memPtr), uint64(memPtr + size));
    }

    /* ------------- N32x32 ------------- */

    function assertEq(N32x32 a, N32x32 b) internal {
        if (N32x32.unwrap(a) != N32x32.unwrap(b)) {
            emit log("Error: a = b not satisfied [N32x32]");
            emit log_named_string("      Left", toString(a));
            emit log_named_string("     Right", toString(b));
            fail();
        }
    }

    function assertGte(N32x32 a, N32x32 b) internal {
        if (N32x32.unwrap(a) < N32x32.unwrap(b)) {
            emit log("Error: a >= b not satisfied [N32x32]");
            emit log_named_string("  Value a", toString(b));
            emit log_named_string("  Value b", toString(a));
            fail();
        }
    }

    function assertGt(N32x32 a, N32x32 b) internal {
        if (N32x32.unwrap(a) <= N32x32.unwrap(b)) {
            emit log("Error: a > b not satisfied [N32x32]");
            emit log_named_string("  Value a", toString(b));
            emit log_named_string("  Value b", toString(a));
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

    /* ------------- UM256 ------------- */

    function assertEq(UM256 A, uint256 s) internal {
        if (!A.eqAllScalar(s)) {
            emit log("Error: A == s not satisfied [UM256]");
            emit log("      Left:");
            logMat(A);
            emit log_named_uint("     Right", s);
            fail();
        }
    }

    function assertLt(UM256 A, uint256 s) internal {
        if (!A.ltAllScalar(s)) {
            emit log("Error: A < s not satisfied [UM256]");
            emit log("      Left:");
            logMat(A);
            emit log_named_uint("     Right", s);
            fail();
        }
    }

    function assertGt(UM256 A, uint256 s) internal {
        if (!A.ltAllScalar(s)) {
            emit log("Error: A > s not satisfied [UM256]");
            emit log("      Left:");
            logMat(A);
            emit log_named_uint("     Right", s);
            fail();
        }
    }

    function assertEq(UM256 A, UM256 B) internal {
        if (!A.eqAll(B)) {
            emit log("Error: A == B not satisfied [UM256]");
            emit log("      Left:");
            logMat(A);
            emit log("     Right:");
            logMat(B);
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

    function assertLt(M32x32 A, N32x32 s) internal {
        if (!A.ltAllScalar(s)) {
            emit log("Error: A < s not satisfied [M32x32]");
            emit log("      Left:");
            logMat(A);
            emit log_named_string("     Right", toString(s));
            fail();
        }
    }

    function assertGt(M32x32 A, N32x32 s) internal {
        if (!A.gtAllScalar(s)) {
            emit log("Error: A > s not satisfied [M32x32]");
            emit log("      Left:");
            logMat(A);
            emit log_named_string("     Right", toString(s));
            fail();
        }
    }

    function assertEq(M32x32 A, uint256 s) internal {
        if (!A.eqAllScalar(N32x32.wrap(int64(int256(s))))) {
            emit log("Error: A == s not satisfied [M32x32]");
            emit log("      Left:");
            logMat(A);
            emit log_named_uint("     Right", s);
            fail();
        }
    }

    // function assertLt(M32x32 A, N32x32 s) internal {
    //     if (!A.ltAllScalar(s)) {
    //         emit log("Error: A < s not satisfied [M32x32]");
    //         emit log("      Left:");
    //         logMat(A);
    //         emit log_named_uint("     Right", s);
    //         fail();
    //     }
    // }

    // function assertGt(M32x32 A, N32x32 s) internal {
    //     if (!A.gtAllScalar(s)) {
    //         emit log("Error: A > s not satisfied [M32x32]");
    //         emit log("      Left:");
    //         logMat(A);
    //         emit log_named_uint("     Right", s);
    //         fail();
    //     }
    // }

    function assertEq(M32x32 A, N32x32 s) internal {
        if (!A.eqAllScalar(s)) {
            emit log("Error: A == s not satisfied [M32x32]");
            emit log("      Left:");
            logMat(A);
            logNum("     Right", s);
            fail();
        }
    }

    function assertEq(M32x32 A, M32x32 B) internal {
        if (!A.eqAll(B)) {
            emit log("Error: A == B not satisfied [M32x32]");
            emit log("      Left:");
            logMat(A);
            emit log("     Right:");
            logMat(B);
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
                assertEq(A.at(i, j), (i == j) ? N32x32Lib.ONE : N32x32Lib.ZERO);
            }
        }
    }

    /* ------------- Array ------------- */

    function rangeIntArray(int256 start, uint256 n, uint256 m) internal pure returns (int256[][] memory array) {
        uint256[][] memory array_ = rangeUintArray(uint256(start), n, m);

        assembly {
            array := array_
        }
    }

    function rangeUintArray(uint256 start, uint256 n, uint256 m) internal pure returns (uint256[][] memory array) {
        array = new uint256[][](n);

        for (uint256 i; i < n; i++) {
            array[i] = new uint256[](m);
        }

        unchecked {
            for (uint256 i; i < n * m; i++) {
                array[i / m][i % m] = start + i;
            }
        }
    }

    /* ------------- Memory ------------- */

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
            A.setUnsafe(0, lenUp - 1, N32x32.wrap(int64(uint64(N32x32Lib.UINT64_MAX))));

            lenUp -= 1;
        }
    }

    /* ------------- log ------------- */

    // function logInt(string memory name, int256 x) internal view {
    //     if (x == type(int256).min) {
    //         console2.log(name, "57896044618658097711785492504343953926634992332820282019728792003956564819968");
    //     } else {
    //         console2.log(name, string.concat(x >= 0 ? "" : "-", vm.toString(x > 0 ? x : -x)));
    //     }
    // }

    function logHeader(M32x32 A) internal view {
        bytes32 data;
        assembly {
            data := mload(A)
        }
        console.logBytes32(data);
    }

    function logNum(N32x32 a) internal {
        logNum("N32x32", a, log_mat_decimals);
    }

    function logNum(string memory name, N32x32 a) internal {
        logNum(name, a, log_mat_decimals);
    }

    function logNum(N32x32 a, uint256 decimals) internal {
        logNum("N32x32", a, decimals);
    }

    function logNum(string memory name, N32x32 a, uint256 decimals) internal {
        string memory repr = toString(a, decimals);

        if (bytes(name).length != 0) repr = string.concat(name, ": ", repr);

        emit log(repr);
    }

    function toString(N32x32 a) internal view returns (string memory repr) {
        return toString(a, log_mat_decimals);
    }

    function toString(N32x32 a, uint256 decimals) internal view returns (string memory repr) {
        int256 ua = int64(N32x32.unwrap(a));
        bool sign = ua < 0;
        uint256 abs = uint256(sign ? -ua : ua);
        uint256 upper = abs >> 32;
        uint256 lower = (uint256(uint32(abs)) * (10 ** decimals) + (1 << 31)) >> 32;

        repr = string.concat(sign ? "-" : "", toString(upper), ".", decimals != 0 ? toString(lower, decimals) : "");

        if (log_mat_extended) repr = string.concat(repr, " [", toHexString(uint64(uint256(ua)), 8), "]");
    }

    function toStringExtended(N32x32 a, uint256 decimals) internal view returns (string memory repr) {
        repr = string.concat(toString(a, decimals), " [", toHexString(uint256(int256(a.unwrap()))), "]");
    }

    function logMat(UM256 A) internal {
        logMat("", A);
    }

    function logMat(string memory name, UM256 A) internal {
        (uint256 n, uint256 m) = A.shape();

        string memory repr = string.concat("\nUM256(", toString(n), ",", toString(m), "): ", name, "\n\n");

        uint256 max = log_mat_max;

        for (uint256 i; i < n && i < max; ++i) {
            repr = string.concat(repr, "\t");
            for (uint256 j; j < m && j < max; ++j) {
                if (j == max - 1 && max < m) repr = string.concat(repr, "..\t");
                else if (i == max - 1 && max < n) repr = string.concat(repr, "..");
                else repr = string.concat(repr, string.concat(toString(A.at(i, j)), " \t"));
            }
            repr = string.concat(repr, "\n");
        }

        emit log(repr);
    }

    function logMat(M32x32 A) internal {
        logMat("", A, log_mat_decimals);
    }

    function logMat(M32x32 A, uint256 decimals) internal {
        logMat("", A, decimals);
    }

    function logMat(string memory name, M32x32 A) internal {
        logMat(name, A, log_mat_decimals);
    }

    function logMat(string memory name, M32x32 A, uint256 decimals) internal {
        (uint256 n, uint256 m) = A.shape();

        string memory repr = string.concat("\nM32x32(", toString(n), ",", toString(m), "): ", name, "\n\n");

        uint256 max = log_mat_max + 1;

        for (uint256 i; i < n && i < max; ++i) {
            repr = string.concat(repr, "\t");
            for (uint256 j; j < m && j < max; ++j) {
                if (j == max - 1 && max < m) repr = string.concat(repr, "..");
                else if (i == max - 1 && max < n) repr = string.concat(repr, "..\t");
                else repr = string.concat(repr, string.concat(toString(A.at(i, j), decimals), " \t"));
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

    /// https://github.com/Vectorized/solady/blob/507e0d84872f435d497e6d2ce10e7f484392db4f/src/utils/LibString.sol#L26-L211
    /// @dev Returns the base 10 decimal representation of `value`.
    function toString(uint256 value) internal pure returns (string memory str) {
        /// @solidity memory-safe-assembly
        assembly {
            // The maximum value of a uint256 contains 78 digits (1 byte per digit), but
            // we allocate 0xa0 bytes to keep the free memory pointer 32-byte word aligned.
            // We will need 1 word for the trailing zeros padding, 1 word for the length,
            // and 3 words for a maximum of 78 digits.
            str := add(mload(0x40), 0x80)
            // Update the free memory pointer to allocate.
            mstore(0x40, add(str, 0x20))
            // Zeroize the slot after the string.
            mstore(str, 0)

            // Cache the end of the memory to calculate the length later.
            let end := str

            let w := not(0) // Tsk.
            // We write the string from rightmost digit to leftmost digit.
            // The following is essentially a do-while loop that also handles the zero case.
            for { let temp := value } 1 { } {
                str := add(str, w) // `sub(str, 1)`.
                // Write the character to the pointer.
                // The ASCII index of the '0' character is 48.
                mstore8(str, add(48, mod(temp, 10)))
                // Keep dividing `temp` until zero.
                temp := div(temp, 10)
                if iszero(temp) { break }
            }

            let length := sub(end, str)
            // Move the pointer 32 bytes leftwards to make room for the length.
            str := sub(str, 0x20)
            // Store the length.
            mstore(str, length)
        }
    }

    function toString(uint256 value, uint256 digits) internal pure returns (string memory str) {
        /// @solidity memory-safe-assembly
        assembly {
            // The maximum value of a uint256 contains 78 digits (1 byte per digit), but
            // we allocate 0xa0 bytes to keep the free memory pointer 32-byte word aligned.
            // We will need 1 word for the trailing zeros padding, 1 word for the length,
            // and 3 words for a maximum of 78 digits.
            str := add(mload(0x40), 0x80)
            // Update the free memory pointer to allocate.
            mstore(0x40, add(str, 0x20))
            // Zeroize the slot after the string.
            mstore(str, 0)

            // Cache the end of the memory to calculate the length later.
            let end := str

            let w := not(0) // Tsk.
            // We write the string from rightmost digit to leftmost digit.
            // The following is essentially a do-while loop that also handles the zero case.
            for { let temp := value } 1 { } {
                str := add(str, w) // `sub(str, 1)`.
                // Write the character to the pointer.
                // The ASCII index of the '0' character is 48.
                mstore8(str, add(48, mod(temp, 10)))
                // Keep dividing `temp` until zero.
                temp := div(temp, 10)
                digits := sub(digits, 1)
                if iszero(digits) { break }
            }

            let length := sub(end, str)
            // Move the pointer 32 bytes leftwards to make room for the length.
            str := sub(str, 0x20)
            // Store the length.
            mstore(str, length)
        }
    }

    // /// @dev Returns the base 10 decimal representation of `value`.
    // function toString(int256 value) internal pure returns (string memory str) {
    //     if (value >= 0) {
    //         return toString(uint256(value));
    //     }
    //     unchecked {
    //         str = toString(uint256(-value));
    //     }
    //     /// @solidity memory-safe-assembly
    //     assembly {
    //         // We still have some spare memory space on the left,
    //         // as we have allocated 3 words (96 bytes) for up to 78 digits.
    //         let length := mload(str) // Load the string length.
    //         mstore(str, 0x2d) // Store the '-' character.
    //         str := sub(str, 1) // Move back the string pointer by a byte.
    //         mstore(str, add(length, 1)) // Update the string length.
    //     }
    // }

    /*´:°•.°+.*•´.*:˚.°*.˚•´.°:°•.°•.*•´.*:˚.°*.˚•´.°:°•.°+.*•´.*:*/
    /*                   HEXADECIMAL OPERATIONS                   */
    /*.•°:°.´+˚.*°.˚:*.´•*.+°.•°:´*.´•*.•°.•°:°.´:•˚°.*°.˚:*.´+°.•*/

    /// @dev Returns the hexadecimal representation of `value`,
    /// left-padded to an input length of `length` bytes.
    /// The output is prefixed with "0x" encoded using 2 hexadecimal digits per byte,
    /// giving a total length of `length * 2 + 2` bytes.
    /// Reverts if `length` is too small for the output to contain all the digits.
    function toHexString(uint256 value, uint256 length) internal pure returns (string memory str) {
        str = toHexStringNoPrefix(value, length);
        /// @solidity memory-safe-assembly
        assembly {
            let strLength := add(mload(str), 2) // Compute the length.
            mstore(str, 0x3078) // Write the "0x" prefix.
            str := sub(str, 2) // Move the pointer.
            mstore(str, strLength) // Write the length.
        }
    }

    /// @dev Returns the hexadecimal representation of `value`,
    /// left-padded to an input length of `length` bytes.
    /// The output is prefixed with "0x" encoded using 2 hexadecimal digits per byte,
    /// giving a total length of `length * 2` bytes.
    /// Reverts if `length` is too small for the output to contain all the digits.
    function toHexStringNoPrefix(uint256 value, uint256 length) internal pure returns (string memory str) {
        /// @solidity memory-safe-assembly
        assembly {
            // We need 0x20 bytes for the trailing zeros padding, `length * 2` bytes
            // for the digits, 0x02 bytes for the prefix, and 0x20 bytes for the length.
            // We add 0x20 to the total and round down to a multiple of 0x20.
            // (0x20 + 0x20 + 0x02 + 0x20) = 0x62.
            str := add(mload(0x40), and(add(shl(1, length), 0x42), not(0x1f)))
            // Allocate the memory.
            mstore(0x40, add(str, 0x20))
            // Zeroize the slot after the string.
            mstore(str, 0)

            // Cache the end to calculate the length later.
            let end := str
            // Store "0123456789abcdef" in scratch space.
            mstore(0x0f, 0x30313233343536373839616263646566)

            let start := sub(str, add(length, length))
            let w := not(1) // Tsk.
            let temp := value
            // We write the string from rightmost digit to leftmost digit.
            // The following is essentially a do-while loop that also handles the zero case.
            for { } 1 { } {
                str := add(str, w) // `sub(str, 2)`.
                mstore8(add(str, 1), mload(and(temp, 15)))
                mstore8(str, mload(and(shr(4, temp), 15)))
                temp := shr(8, temp)
                if iszero(xor(str, start)) { break }
            }

            if temp {
                // Store the function selector of `HexLengthInsufficient()`.
                mstore(0x00, 0x2194895a)
                // Revert with (offset, size).
                revert(0x1c, 0x04)
            }

            // Compute the string's length.
            let strLength := sub(end, str)
            // Move the pointer and write the length.
            str := sub(str, 0x20)
            mstore(str, strLength)
        }
    }

    /// @dev Returns the hexadecimal representation of `value`.
    /// The output is prefixed with "0x" and encoded using 2 hexadecimal digits per byte.
    /// As address are 20 bytes long, the output will left-padded to have
    /// a length of `20 * 2 + 2` bytes.
    function toHexString(uint256 value) internal pure returns (string memory str) {
        str = toHexStringNoPrefix(value);
        /// @solidity memory-safe-assembly
        assembly {
            let strLength := add(mload(str), 2) // Compute the length.
            mstore(str, 0x3078) // Write the "0x" prefix.
            str := sub(str, 2) // Move the pointer.
            mstore(str, strLength) // Write the length.
        }
    }

    /// @dev Returns the hexadecimal representation of `value`.
    /// The output is encoded using 2 hexadecimal digits per byte.
    /// As address are 20 bytes long, the output will left-padded to have
    /// a length of `20 * 2` bytes.
    function toHexStringNoPrefix(uint256 value) internal pure returns (string memory str) {
        /// @solidity memory-safe-assembly
        assembly {
            // We need 0x20 bytes for the trailing zeros padding, 0x20 bytes for the length,
            // 0x02 bytes for the prefix, and 0x40 bytes for the digits.
            // The next multiple of 0x20 above (0x20 + 0x20 + 0x02 + 0x40) is 0xa0.
            str := add(mload(0x40), 0x80)
            // Allocate the memory.
            mstore(0x40, add(str, 0x20))
            // Zeroize the slot after the string.
            mstore(str, 0)

            // Cache the end to calculate the length later.
            let end := str
            // Store "0123456789abcdef" in scratch space.
            mstore(0x0f, 0x30313233343536373839616263646566)

            let w := not(1) // Tsk.
            // We write the string from rightmost digit to leftmost digit.
            // The following is essentially a do-while loop that also handles the zero case.
            for { let temp := value } 1 { } {
                str := add(str, w) // `sub(str, 2)`.
                mstore8(add(str, 1), mload(and(temp, 15)))
                mstore8(str, mload(and(shr(4, temp), 15)))
                temp := shr(8, temp)
                if iszero(temp) { break }
            }

            // Compute the string's length.
            let strLength := sub(end, str)
            // Move the pointer and write the length.
            str := sub(str, 0x20)
            mstore(str, strLength)
        }
    }
}
