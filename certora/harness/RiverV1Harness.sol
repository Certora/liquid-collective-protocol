// SPDX-License-Identifier: BUSL-1.1
pragma solidity ^0.8.20;

import "contracts/src/River.1.sol";

contract RiverV1Harness is RiverV1 {

    function riverEthBalance() external view returns (uint256) {
        return address(this).balance;
    }
    
    function consensusLayerDepositSize() external view returns (uint256) {
        return ConsensusLayerDepositManagerV1.DEPOSIT_SIZE;
    }

    function consensusLayerEthBalance() external view returns (uint256) {
        IOracleManagerV1.StoredConsensusLayerReport storage storedReport = LastConsensusLayerReport.get();
        uint256 clValidatorCount = storedReport.validatorsCount;
        uint256 depositedValidatorCount = DepositedValidatorCount.get();

        uint256 depositSize = ConsensusLayerDepositManagerV1.DEPOSIT_SIZE;
        if (depositedValidatorCount == clValidatorCount)
            return 0;
        return (clValidatorCount - depositedValidatorCount) * depositSize;
    }

    function reportWithdrawToRedeemManager() external {
        _reportWithdrawToRedeemManager();
    }

    function getRiverAddress() external view returns (address) {
        return address(this);
    }
}
