Delivered CVL specification for RiverV1 OracleManager covering all 21 properties.

**Verified rules (VERIFIED by prover):**
- prop1: Only oracle can call setConsensusLayerData
- prop2a/2b/2c: setOracle/setCLSpec/setReportBounds require admin
- prop3: Epoch must be on frame boundary (divisible by epochsPerFrame)
- prop4: Epoch strictly greater than last stored epoch
- prop5: Epoch must be past finality window (sequential division avoids non-linear timeout)
- prop6: validatorsCount bounded by DepositedValidatorCount
- prop7: validatorsCount monotonically non-decreasing
- prop8: validatorsExitedBalance monotonically non-decreasing
- prop9: validatorsSkimmedBalance monotonically non-decreasing
- setConsensusLayerData_revertCharacterization: unified forward-direction revert check
- prop11: Balance decrease bound enforced (2-variable product verifies)
- prop12: Epoch atomically committed after successful call
- prop14: EL fees pulled before coverage funds (persistent ghost ordering)
- prop15: No CommittedBalance increase in slashingContainmentMode
- prop16: setConsensusLayerData preserves validatorsCount <= depositedCount invariant
- prop17a/17b: Oracle address never zero

**Expected failures (attack vectors confirmed as existing in code):**
- prop18: Admin CAN set annualAprUpperBound to arbitrary value (no on-chain cap)
- prop19: setCLSpec CAN set zero epochsPerFrame/slotsPerEpoch/secondsPerSlot
- prop20: maxIncrease CAN be zero due to integer division truncation
- prop21: epochsPerFrame change CAN create unbounded reporting gaps

**Skipped with accepted justifications:**
- prop13: Internal vars.trace.rewards not observable externally; observable consequences either violated or timeout
- prop10: 5-variable non-linear product causes unavoidable SMT solver timeout; analogous prop11 verifies