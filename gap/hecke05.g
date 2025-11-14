#############################################################################
##
##  H(G5)
##
Read("support.g");

HeckeCRG05:= function(params)
    local   C3Elt,  M,  N,  mmm,  c0,  c1,  c2,  null,  one,  setter,
            basicVec,  vecUnderWord,  img,  rel,  gen,  inv,  setRow,
            makeEdge,  u,  u1,  k,  z,  zs,  ts,  xs;

    # constructor
    C3Elt:= MakeC3Elts(params[1]);

    # matrices.  -1 mod 7 = 6 and -2 mod 7 = 5
    M:= 9;  N:= 24;
    mmm:= List([1..M-1], x-> []);

    # name some C3Elts
    c0:= params[1][1];  c1:= params[1][2];  c2:= params[1][3];
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
    for k in 4*[0..5] do
        setRow(k+1, 1, basicVec(k+1, u), img);
        setRow(k+1, -1, basicVec(k+1, u1), img);
    od;

    # spanning tree
    for k in 4*[0..5] do
        makeEdge(k+1, k+2, 3);
        makeEdge(k+2, k+3, -2);
        makeEdge(k+3, k+4, 3);
    od;

    # *z
    for k in [0..19] do
        makeEdge(k+1, k+5, 4);
    od;

    for k in 4*[0..5] do
        setRow(k+2, 1, [ -2, 3 ], rel);
        setRow(k+4, -1, [ -3, 2 ], rel);
    od;

    for k in 4*[0..4] do
        setRow(k+2, 2, [ -3, -1, 4 ], rel);
        setRow(k+5, -2, [ -4, 1, 3 ], rel);
        setRow(k+5, 2, 0, gen);
        setRow(k+3, -2, 0, inv);
    od;

    for k in 4*[0..4] do
        setRow(k+6, -1, [ -3, 2 ], rel);
        setRow(k+8, 1, 0, gen);
    od;

    for k in 4*[0..4] do
        setRow(k+2, 3, [ 2, 1 ], rel);
        setRow(k+4, 3, [ -3, 4 ], rel);
        setRow(k+5, -3, [ -1, -2 ], rel);
        setRow(k+7, -3, [ -4, 3 ], rel);
    od;

    for k in 4*[0..4] do
        setRow(k+3, 1, [ -2, 3 ], rel);
    od;

    for k in 4*[0..3] do
        setRow(k+12, -2, [ 1, -3 ], rel);
        setRow(k+7, -1, 0, inv);
    od;

    for k in 4*[0..3] do
        setRow(k+4, 2, [ 3, -1 ], rel);
    od;
    setRow(20, 2, 0, gen);
    setRow(4, -2, 0, inv);
    setRow(8, -2, 0, inv);

    setRow(4, 1, [ -2, 3 ], rel);
    setRow(23, -1, [ -3, 2 ], rel);
    setRow(23, 1, 0, gen);
    setRow(2, -1, 0, inv);
    setRow(3, -1, 0, inv);

    setRow(1, 2, [ 3, -1 ], rel);
    setRow(1, -2, 0, inv);

    setRow(1, -3, [ -1, -2 ], rel);

    setRow(3, -3, [ 3, -2, -3, -1 ], rel);

    setRow(23, -2, [ 1, -3 ], rel);
    setRow(22, 2, 0, gen);
    setRow(24, 2, 0, gen);

    setRow(22, 3, [ 2, 1 ], rel);
    setRow(24, 3, [ 2, 1 ], rel);

    for k in [21..24] do
        setRow(k, 4, [ 3, 3 ], rel);
    od;

    for k in [1..4] do
        setRow(k, -4, [ -3, -3 ], rel);
    od;

    z:= [1,2,1,2];
    zs:= [[]];
    for k in [2..6] do
        zs[k]:= Concatenation(zs[k-1], z);
    od;

    ts:= [[], [1], [1,1]];
    xs:= [[], [2,1], [2,1,-2], [2,1,1]];

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

GenericHeckeCRG05:= function()
    local   b0,  b1,  b2,  c0,  c1,  c2;

    ## indeterminates
    b0:= Mvp("b0");  b1:= Mvp("b1");  b2:= Mvp("b2");
    c0:= Mvp("c0");  c1:= Mvp("c1");  c2:= Mvp("c2");

    return HeckeCRG05([[c0, c1, c2], [b0, b1, b2]]);
end;

TestGenericHeckeCRG05:= function()
    local   hecke,  mmm,  M,  params,  b0,  b1,  b2,  c0,  c1,  c2,
            test,  m12,  m2;

    hecke:= GenericHeckeCRG05();

    mmm:= hecke.matgens;
    M:= Length(mmm) + 1;
    params:= hecke.params;
    c0:= params[1][1];  c1:= params[1][2];  c2:= params[1][3];
    b0:= params[2][1];  b1:= params[2][2];  b2:= params[2][3];

    test:= rec(relations:= [], powers:= []);

    Print("testing relation ... \c");
    m12:= mmm[1] * mmm[2];
    test.relations[1]:= m12 * m12 = mmm[2] * m12 * mmm[1];
    Print(test.relations[1], "\n");

    Print("testing power ... \c");
    m2:= mmm[1] * mmm[1];
    test.powers[1]:=
      m2 * mmm[1] = c2 * m2 + c1 * mmm[1] + c0 * mmm[1] * mmm[-1 mod M];
    Print(test.powers[1], "\n");

    Print("testing power ... \c");
    m2:= mmm[2] * mmm[2];
    test.powers[2]:=
      m2 * mmm[2] = b2 * m2 + b1 * mmm[2] + b0 * mmm[2] * mmm[-2 mod M];
    Print(test.powers[2], "\n");

    return test;
end;

test:= function()
    local   hecke,  gram,  det;
    hecke:= GenericHeckeCRG05();
    gram:= GramMatrix(hecke);
    det:= DeterminantMat(gram.gram);
    Print("det = ", det, "\n");
end;
