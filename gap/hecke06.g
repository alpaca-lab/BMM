#############################################################################
##
##  H(G6)
##
Read("support.g");

HeckeCRG06:= function(params)
    local   C3Elt,  M,  N,  mmm,  c0,  c1,  c2,  null,  one,  setter,
            basicVec,  vecUnderWord,  img,  rel,  gen,  inv,  setRow,
            makeEdge,  u,  u1,  k,  z,  zs,  ts,  xs;

    # constructor
    C3Elt:= MakeC3Elts(params[2]);

    # matrices.  -1 mod 7 = 6 and -2 mod 7 = 5
    M:= 7;  N:= 16;
    mmm:= List([1..M-1], x-> []);

    # name some C3Elts
    c0:= params[2][1];  c1:= params[2][2];  c2:= params[2][3];
    null:= C3Elt([0*c0, 0*c0, 0*c0]);    # 0
    one:= C3Elt([c0^0, 0*c0, 0*c0]);     # 1

    setter:= MakeSetter(M, N, null, one, mmm, params);
    basicVec:= setter.basicVec;
    vecUnderWord:= setter.vecUnderWord;
    img:= setter.img;  rel:= setter.rel;
    gen:= setter.gen;  inv:= setter.inv;
    setRow:= setter.setRow;
    makeEdge:= setter.makeEdge;

    # subgroup table
    u:= C3Elt([0*c0, c0^0, 0*c0]);         # u
    u1:= c0^-1 * C3Elt([-c1, -c2, c0^0]);  # u'
    for k in 4*[0..3] do
        setRow(k+1, 2, basicVec(k+1, u), img);
        setRow(k+1, -2, basicVec(k+1, u1), img);
    od;

    # spanning tree
    for k in 4*[0..3] do
        makeEdge(k+1, k+2, 1);
        makeEdge(k+2, k+3, 2);
        makeEdge(k+3, k+4, 1);
    od;

    # cycles
    for k in 4*[0..3] do
        setRow(k+2, 1, 0, gen);
        setRow(k+1, -1, 0, inv);
        setRow(k+4, 1, 0, gen);
        setRow(k+3, -1, 0, inv);
    od;

    # *z
    for k in [0..11] do
        makeEdge(k+1, k+5, 3);
    od;

    for k in 4*[0..2] do
        setRow(k+4, 2, [ -1, -2, -1, -2, -1, 3 ], rel);
        setRow(k+4, -2, 0, inv);
    od;

    for k in 4*[0..2] do
        setRow(k+6, -2, [ -3, 1, 2, 1, 2, 1 ], rel);
        setRow(k+7, 2, 0, gen);
    od;

    setRow(3, 2, [ -1, -2, -1, -2, -1, 3 ], rel);
    setRow(2, -2, 0, inv);

    setRow(16, -2, [ -3, 1, 2, 1, 2, 1 ], rel);
    setRow(16, 2, 0, gen);

    for k in [13..16] do
        setRow(k, 3, [ 1, 2, 1, 2, 1, 2 ], rel);
    od;

    for k in [1..4] do
        setRow(k, -3, [ -2, -1, -2, -1, -2, -1 ], rel);
    od;

    z:= [1,2,1,2,1,2];
    zs:= [[]];
    for k in [2..4] do
        zs[k]:= Concatenation(zs[k-1], z);
    od;

    ts:= [[], [2], [2,2]];
    xs:= [[], [1], [1,2], [1,2,1]];

    return rec(
      matgens := mmm,
      params:= params,
      zs:= zs,  ts:= ts,  xs:= xs,
      one:= one,
      basicVec:= basicVec,
      vecUnderWord:= vecUnderWord,
      words:= List(Cartesian(zs, xs), Concatenation) # coset reps
    );

end;

GenericHeckeCRG06:= function()
    local   a0,  a1,  c0,  c1,  c2;

    ## indeterminates
    a0:= Mvp("a0");  a1:= Mvp("a1");  # b, a
    c0:= Mvp("c0");  c1:= Mvp("c1");  c2:= Mvp("c2");  # e, d, c

    return HeckeCRG06([[a0, a1], [c0, c1, c2]]);
end;

TestGenericHeckeCRG06:= function()
    local   hecke,  mmm,  M,  params,  a0,  a1,  c0,  c1,  c2,  test,
            m12,  m212,  m121,  m2;

    hecke:= GenericHeckeCRG06();

    mmm:= hecke.matgens;
    M:= Length(mmm) + 1;
    params:= hecke.params;
    a0:= params[1][1];  a1:= params[1][2];
    c0:= params[2][1];  c1:= params[2][2];  c2:= params[2][3];

    test:= rec(relations:= [], powers:= []);

    Print("testing relation ... \c");
    m12:= mmm[1] * mmm[2];
    m212:= mmm[2] * m12;
    m121:= m12 * mmm[1];
    test.relations[1]:= m212 * m121 = m121 * m212;
    Print(test.relations[1], "\n");

    Print("testing power ... \c");
    test.powers[1]:=
      mmm[1] * mmm[1] = a1 * mmm[1] + a0 * mmm[1] * mmm[-1 mod M];
    Print(test.powers[1], "\n");

    Print("testing power ... \c");
    m2:= mmm[2] * mmm[2];
    test.powers[2]:=
      m2 * mmm[2] = c2 * m2 + c1 * mmm[2] + c0 * mmm[2] * mmm[-2 mod M];
    Print(test.powers[2], "\n");

    return test;
end;

test:= function()
    local   hecke,  gram,  det;
    hecke:= GenericHeckeCRG06();
    gram:= GramMatrix(hecke);
    det:= DeterminantMat(gram.gram);
    Print("det = ", det, "\n");
end;
