import "Base.spec";

// ~ 3m
// https://prover.certora.com/output/6893/911e1c0b62134b20b5058adc8116e305/?anonymousKey=5ab872721f4ee1e87537ba68fae9954c03837843
rule depositRevertsIfUserDenied(env e)
{
    deposit@withrevert(e);
    bool reverted = lastReverted;
    assert AL.isDenied(e.msg.sender) => reverted;
}

// ~ 2m
// https://prover.certora.com/output/6893/dda9d7760bb445c4afcc6a7b4cfeeeff/?anonymousKey=5cff8d1009d9f7b37b4267f3a2350d4b15835c64
rule depositAdditivitySplittingNotProfitable(env e1, env e2, env eSum) {
    mathint amount1 = to_mathint(e1.msg.value);
    mathint amount2 = to_mathint(e2.msg.value);
    address recipient;
    require recipient != getRiverAddress(e1);
    require amount1 + amount2 == to_mathint(eSum.msg.value);

    mathint sharesBefore = balanceOf(recipient);
    storage initial = lastStorage;

    depositAndTransfer(e1, recipient);
    depositAndTransfer(e2, recipient);
    mathint shares1 = balanceOf(recipient);

    depositAndTransfer(eSum, recipient) at initial;
    mathint sharesSum = balanceOf(recipient);

    assert shares1 <= sharesSum;
}

// ~ 11m
// https://prover.certora.com/output/6893/0b373abbfb5c40d0a60986ab8fb5583d/?anonymousKey=143734f9d61e7daa05eb35bce851f1892e8782c2
rule onlyOneAddressCanCall(method f, calldataarg args)
{
    env e1;
    env e2;
    require e1.msg.sender != e2.msg.sender;
    storage initStorage = lastStorage;
    f@withrevert(e1, args);
    bool reverted1 = lastReverted;
    f@withrevert(e2, args);
    bool reverted2 = lastReverted;
    assert !reverted1 => reverted2;
}

// ~ 30m
// https://prover.certora.com/output/6893/8a0dd9e29a0544cd9266ba508b2ebd53/?anonymousKey=e921b0b4ed6f4c0720dc96ac6b324358f98a22f9
invariant totalSupplyBasicIntegrity()
    totalSupply() == sharesFromUnderlyingBalance(totalUnderlyingSupply());

