//SPDX-License-Identifier: BUSL-1.1
pragma solidity 0.8.20;

import { LibErrors } from "contracts/src/libraries/LibErrors.sol";

interface IRiver {
    function sendRedeemManagerExceedingFunds() external payable;
    function underlyingBalanceFromShares(uint256 _shares) external view returns (uint256);
    function transferFrom(address _from, address _to, uint256 _value) external returns (bool);
}

contract RiverMock is IRiver {
    address public redeemManagerAddress;
    uint256 public totalShares;
    uint256 public assetBalance;
    mapping(address => uint256) public sharesPerOwner;

    error BalanceTooLow();

    modifier hasFunds(address _owner, uint256 _value) {
        if (sharesPerOwner[_owner] < _value) {
            revert BalanceTooLow();
        }
        _;
    }

    function sendRedeemManagerExceedingFunds() external payable {
        if (msg.sender != redeemManagerAddress) {
            revert LibErrors.Unauthorized(msg.sender);
        }
    }

    function underlyingBalanceFromShares(uint256 _shares) external view returns (uint256) {
        return _balanceFromShares(_shares);
    }

    function transferFrom(address _from, address _to, uint256 _value) external hasFunds(_from, _value) returns (bool) {
        if (_to == address(0)) revert("Zero address");
        return _transfer(_from, _to, _value);
    }

    function _transfer(address _from, address _to, uint256 _value) internal returns (bool) {
        sharesPerOwner[_from] -= _value;
        sharesPerOwner[_to] += _value;

        return true;
    }

    /// @notice Internal utility to retrieve the underlying asset balance for the given shares
    /// @param _shares Amount of shares to convert
    /// @return The balance from the given shares
    function _balanceFromShares(uint256 _shares) internal view returns (uint256) {
        if (totalShares == 0) {
            return 0;
        }

        return RiverMath.mulDiv(_shares, assetBalance, totalShares);
    }
}

library RiverMath {
    function mulDiv(uint256 x, uint256 y, uint256 z) internal pure returns (uint256) {
        return (x * y) / z;
    }
}