Successfully formalized all 20 security properties for RiverV1 River Core (Admin & Redemptions) component. 

## Summary

All rules are VERIFIED and the feedback judge has accepted the specification.

### Properties Coverage

**Properties 1-12 (Safety Properties)**:
- Prop 1: `prop1_onlyAdminCanCallSetters` - Parametric rule verifying all config setters revert for non-admin callers (12 setters verified)
- Prop 2: `prop2_slashingModeBlocksRequestRedeem` - requestRedeem reverts in slashing containment mode
- Prop 3: `prop3_deniedOrNoRedeemMaskBlocksRedeem` - requestRedeem reverts if caller is denied or lacks REDEEM_MASK
- Prop 4: `prop4_deniedRecipientBlocksRedeem` - requestRedeem reverts if recipient is denied
- Prop 5: `prop5_requestRedeemShareTransfer` - Share balance changes exactly ±_lsETHAmount, totalSupply unchanged
- Props 6-9: Sender guard rules for sendELFees, sendCLFunds, sendCoverageFunds, sendRedeemManagerExceedingFunds
- Prop 10: `prop10_setGlobalFeeValidation` - Biconditional: reverts iff fee > 10000
- Props 11a-e: Setter effect rules verifying exact storage and no side effects
- Props 12a-d: Zero address rejection rules for address setters

**Properties 13-16 (Invariants)**:
- Prop 13: `prop13_globalFeeLEMaxBasisPoints` - CVL invariant checking globalFee <= 10000
- Props 14-16: Combined inductive rule `prop14_15_16_nonZeroAddresses` + companion init rules for each
  - Once AllowlistAddress, ELFeeRecipientAddress, CollectorAddress are non-zero, no function can zero them
  - Note: upgradeable proxy pattern requires inductive rules instead of pure invariants

**Properties 17-20 (Attack Vectors)**:
- All formalized using `satisfy` rules to demonstrate the attacks ARE possible:
  - Prop 17: Admin can instantly set max fee (no time-lock)
  - Prop 18: claimRedeemRequests can revert (deny-list attack possible)
  - Prop 19: Exchange rate can exceed 1:1 (front-running advantage exists)
  - Prop 20: Old ELFeeRecipient is locked out after address rotation

### Key Technical Decisions
1. Attack vectors (props 17-20) use `satisfy` instead of `assert` to demonstrate vulnerabilities exist
2. Props 14-16 use inductive rules (not invariants) due to upgradeable proxy not calling init in constructor
3. Combined props 14-16 into single parametric rule to reduce compute overhead
4. Several methods excluded from parametric invariant checking due to HAVOC/compute constraints (all excluded methods confirmed to not modify tracked state)
5. Property 7 uses uint160 cast chain for bytes32 → address conversion for withdrawal credentials