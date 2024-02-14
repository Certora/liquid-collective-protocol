//SPDX-License-Identifier: BUSL-1.1
pragma solidity 0.8.20;

import {LibUint256} from "contracts/src/libraries/LibUint256.sol";

interface IRegistry {
    function pickNextValidatorsToDeposit(uint256 _count) external returns (bytes[] memory publicKeys, bytes[] memory signatures);
}

contract OperatorsRegistryMock is IRegistry {
    /// @notice Size of a BLS Public key in bytes
    uint256 public constant PUBLIC_KEY_LENGTH = 48;
    /// @notice Size of a BLS Signature in bytes
    uint256 public constant SIGNATURE_LENGTH = 96;

    uint256 private _fundableOperatorCount;
    uint256 private _opIndex;
    mapping(uint256 => uint256) private _availableKeysPerIndex;
    mapping(uint256 => bytes) private signaturesPerOp;
    mapping(uint256 => bytes) private publicKeysPerOp;
    

    function pickNextValidatorsToDeposit(uint256 _count) external returns (bytes[] memory, bytes[] memory) {
        
        uint256 totalKeysCount = LibUint256.min(_availableKeysPerIndex[_opIndex], _count);

        bytes[] memory publicKeys = new bytes[](totalKeysCount);
        bytes[] memory signatures = new bytes[](totalKeysCount);

        // we loop on all operators
        for (uint256 idx = 0; idx < totalKeysCount; ++idx) {
            require (publicKeysPerOp[idx].length == PUBLIC_KEY_LENGTH, "Invalid length");
            require (signaturesPerOp[idx].length == SIGNATURE_LENGTH, "Invalid length");
            publicKeys[idx] = publicKeysPerOp[_opIndex + idx];
            signatures[idx] = signaturesPerOp[_opIndex + idx];
        }
        _opIndex += _count;
        
        return (publicKeys, signatures);
    }
}
