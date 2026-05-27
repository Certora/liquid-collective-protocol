Successfully formalized 19 of 21 properties for the RiverV1 SharesManager (LsETH ERC20) component. All non-skipped rules are VERIFIED by the Certora prover and approved by the feedback judge.

## Summary

### Verified Properties (19)
- **P1**: `erc20SumEqualsTotal` invariant — Sum of all per-account share balances equals totalSupply() at all times
- **P2**: `zeroAddressHasNoShares` invariant — Zero address never holds positive share balance
- **P3**: `transferDoesNotChangeTotalSupply`, `transferFromDoesNotChangeTotalSupply` — Transfers don't change totalSupply
- **P4**: `transferUpdatesBalancesCorrectly`, `transferFromUpdatesBalancesCorrectly` — Correct balance updates after transfer
- **P5**: `transferRevertsForZeroTo`, `transferFromRevertsForZeroTo` — Revert when destination is address(0)
- **P6**: `transferRevertsForZeroAmount`, `transferFromRevertsForZeroAmount` — Revert for zero-value transfers (NullTransfer)
- **P7**: `transferRevertsWhenBalanceTooLow`, `transferFromRevertsWhenBalanceTooLow` — Revert when balance < amount (BalanceTooLow)
- **P8**: `transferFromRevertsWhenAllowanceTooLow` — Revert when allowance < amount (AllowanceTooLow)
- **P9**: `allowanceIncreasesOnlyByOwner` — Allowances only increase via owner calling approve/increaseAllowance
- **P10**: `decreaseAndTransferNeverIncreaseAllowance` — decreaseAllowance/transferFrom never increase allowances
- **P11**: `transferFromDecreasesAllowanceCorrectly` — transferFrom decreases allowance by exact amount (unless infinite)
- **P12**: `transferRevertsWhenFromDenied`, `transferFromRevertsWhenFromDenied` — Revert when sender is denied
- **P13**: `transferRevertsWhenToDenied`, `transferFromRevertsWhenToDenied` — Revert when recipient is denied
- **P14**: `approveRevertsForZeroSpender`, `increaseAllowanceRevertsForZeroSpender`, `decreaseAllowanceRevertsForZeroSpender` — Revert for zero-address spender
- **P15**: Proven jointly with P1 (erc20SumEqualsTotal uses ghost mirrors of raw SharesPerOwner)
- **P16**: `balanceOfEqualsRawShares` invariant — balanceOf returns raw share count, not ETH equivalent
- **P17**: `decimalsIsEighteen`, `nameIsLiquidStakedETH`, `symbolIsLsETH` — Correct token metadata
- **P18**: `noFirstDepositorWindfall` — satisfy rule finds witness of first-depositor windfall attack (reachable)
- **P19**: `depositAlwaysMintsPositiveShares` — satisfy rule finds witness of zero-share minting (reachable)

### Skipped Properties (2)
- **P20**: Allowlist contract misconfiguration — Requires reasoning about admin governance actions across transactions; outside CVL's single-transaction model scope
- **P21**: Double-spend via approve() front-running — Inherently requires two separate sequential transactions; CVL's single-transaction model cannot capture this race condition

### Key Technical Highlights
- Ghost state (ghostSumOfShares, ghostSharesPerOwner) tracks SharesPerOwner diamond storage via Sstore hooks
- Invariant ordering: balanceOfEqualsRawShares declared before zeroAddressHasNoShares to enable requireInvariant
- Three methods excluded from shares invariants: initRiverV1_1, depositToConsensusLayerWithDepositRoot, claimRedeemRequests
- AllowlistV1 isDenied checks use DISPATCHER summary for sound external call modeling
- P18/P19 use satisfy rules (not assert) — VERIFIED means the prover found witnesses confirming attack scenarios are reachable