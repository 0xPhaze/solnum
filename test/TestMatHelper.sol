// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "src/SolMat64.sol";
import "forge-std/Test.sol";

using SolMat64 for Mat64;

contract TestMatHelper is Test {
    /* ------------- helpers ------------- */

    function assertEq(Mat64 a, uint256 v) internal {
        if (!a.eq(v)) {
            emit log("Error: a == b not satisfied [Mat64]");
            emit log_named_uint("  Expected", v);
            emit log("    Actual");
            logMat(a);
            fail();
        }
    }

    function assertEq(Mat64 a, Mat64 b) internal {
        if (!a.eq(b)) {
            emit log("Error: a == b not satisfied [Mat64]");
            emit log("  Expected");
            logMat(b);
            emit log("    Actual");
            logMat(a);
            fail();
        }
    }

    function assertNEq(Mat64 a, Mat64 b) internal {
        if (a.eq(b)) {
            emit log("Error: a != b not satisfied [Mat64]");
            logMat(b);
            fail();
        }
    }

    function assertIsEye(Mat64 A) internal {
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

    function lognewHeader(Mat64 A) internal view {
        bytes32 data;
        assembly {
            data := mload(A)
        }
        console.logBytes32(data);
    }

    function logMat(Mat64 A) public {
        (uint256 n, uint256 m) = A.shape();

        string memory str = string.concat("\nMat(", vm.toString(n), ",", vm.toString(m), "):\n");

        uint256 MAX = 10;

        for (uint256 i; i < n && i < MAX; ++i) {
            for (uint256 j; j < m && j < MAX; ++j) {
                if (i == MAX - 1) str = string.concat(str, "..\t");
                else str = string.concat(str, string.concat(vm.toString(A.at(i, j)), " \t"));
                if (j == MAX - 1) str = string.concat(str, "..");
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

    // function logMem(Mat64 A) public {
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
