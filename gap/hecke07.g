#############################################################################
##
##  H(G7)
##
Read("support.g");

HeckeCRG07:= function(params)
    local   C3Elt,  M,  N,  mmm,  c0,  c1,  c2,  null,  one,  setter,
            basicVec,  vecUnderWord,  img,  rel,  gen,  inv,  setRow,
            makeEdge,  u,  u1,  k,  z,  zs,  ts,  xs;

    # constructor
    C3Elt:= MakeC3Elts(params[3]);

    # matrices.  -1 mod 9 = 8, -2 mod 9 = 7 and -3 mod 9 = 6
    M:= 9;  N:= 48;
    mmm:= List([1..M-1], x-> []);

    # name some C3Elts
    c0:= params[3][1];  c1:= params[3][2];  c2:= params[3][3];
    null:= C3Elt([0*c0, 0*c0, 0*c0]); # 0
    one:= C3Elt([c0^0, 0*c0, 0*c0]);  # 1

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
    for k in 4*[0..11] do
        setRow(k+1, 3, basicVec(k+1, u), img);
        setRow(k+1, -3, basicVec(k+1, u1), img);
    od;

    # spanning tree
    for k in 4*[0..11] do
        makeEdge(k+1, k+2, 1);
        makeEdge(k+2, k+3, 3);
        makeEdge(k+3, k+4, 1);
    od;

    # cycles
    for k in 4*[0..11] do
        setRow(k+2, 1, 0, gen);
        setRow(k+4, 1, 0, gen);
        setRow(k+1, -1, 0, inv);
        setRow(k+3, -1, 0, inv);
    od;

    # z*
    for k in [0..43] do
        makeEdge(k+1, k+5, 4);
    od;

    for k in 4*[0..10] do
        setRow(k+2, 2, [ -1, -3, 4 ], rel);
        setRow(k+4, 2, [ -1, -3, 4 ], rel);
        setRow(k+5, -2, [ -4, 3, 1 ], rel);
        setRow(k+6, -2, [ -4, 3, 1 ], rel);
    od;

    for k in 4*[0..9] do
        setRow(k+9, 2, 0, gen);
        setRow(k+4, -2, 0, inv);
    od;

    for k in 4*[0..8] do
        setRow(k+4, 3, [ -2, -1, 4 ], rel);
        setRow(k+14, -3, [ -4, 1, 2 ], rel);
        setRow(k+15, 3, 0, gen);
    od;

    for k in 4*[0..6] do
        setRow(k+12, -3, 0, inv);
    od;

    for k in 4*[0..6] do
        setRow(k+7, 2, [ -1, 4, -3 ], rel);
    od;

    for k in 4*[0..7] do
        setRow(k+19, -2, [ -4, 3, 1 ], rel);
    od;

    for k in 4*[0..2] do
        setRow(k+35, 2, 0, gen);
        setRow(k+7, -2, 0, inv);
    od;

    for k in 4*[0..2] do
        setRow(k+3, 3, [ 4, -2, -1 ], rel);
        setRow(k+40, -3, [ -4, 1, 2 ], rel);
    od;

    setRow(3, -2, [ 3, -4, 1 ], rel);
    setRow(48, 3, 0, gen);

    for k in 4*[0..2] do
        setRow(k+2, -3, 0, inv);
    od;
    setRow(4, -3, 0, inv);
    setRow(8, -3, 0, inv);
    setRow(40, 3, 0, gen);
    setRow(44, 3, 0, gen);

    setRow(1, 2, [ -1, -3, 4 ], rel);
    setRow(3, 2, [ -1, -3, 4 ], rel);
    setRow(5, 2, [ -1, -3, 4 ], rel);

    setRow(1, -2, 0, inv);
    setRow(2, -2, 0, inv);

    setRow(44, -2, [ -4, 3, 1 ], rel);
    setRow(48, -2, [ -4, 3, 1 ], rel);

    setRow(46, 2, 0, gen);
    setRow(47, 2, 0, gen);
    setRow(48, 2, 0, gen);

    for k in [45..48] do
        setRow(k, 4, [ 1, 2, 3], rel);
    od;

    for k in [1..4] do
        setRow(k, -4, [ -3, -2, -1 ], rel);
    od;

    z:= [1,2,3];
    zs:= [[]];
    for k in [2..12] do
        zs[k]:= Concatenation(zs[k-1], z);
    od;

    ts:= [[], [3], [3,3]];
    xs:= [[], [1], [1,3], [1,3,1]];

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

GenericHeckeCRG07:= function()
    local   a0,  a1,  b0,  b1,  b2,  c0,  c1,  c2;

    ## indeterminates
    a0:= Mvp("a0");  a1:= Mvp("a1");
    b0:= Mvp("b0");  b1:= Mvp("b1");  b2:= Mvp("b2");
    c0:= Mvp("c0");  c1:= Mvp("c1");  c2:= Mvp("c2");

    return HeckeCRG07([[a0, a1], [b0, b1, b2], [c0, c1, c2]]);
end;

TestGenericHeckeCRG07:= function()
    local   hecke,  mmm,  M,  params,  a0,  a1,  b0,  b1,  b2,  c0,
            c1,  c2,  test,  m2;

    hecke:= GenericHeckeCRG07();

    mmm:= hecke.matgens;
    M:= Length(mmm) + 1;
    params:= hecke.params;
    a0:= params[1][1];  a1:= params[1][2];
    b0:= params[2][1];  b1:= params[2][2];  b2:= params[2][3];
    c0:= params[3][1];  c1:= params[3][2];  c2:= params[3][3];

    test:= rec(relations:= [], powers:= []);

    Print("testing relations ... \c");
    test.relations[1]:=
      mmm[1] * mmm[2] * mmm[3] = mmm[2] * mmm[3] * mmm[1];
    Print(test.relations[1], "\n");
    test.relations[2]:=
      mmm[1] * mmm[2] * mmm[3] = mmm[3] * mmm[1] * mmm[2];
    Print(test.relations[2], "\n");

    Print("testing powers ... \c");
    test.powers[1]:=
      mmm[1] * mmm[1] = a1 * mmm[1] + a0 * mmm[1] * mmm[-1 mod M];
    Print(test.powers[1], "\n");
    m2:= mmm[2] * mmm[2];
    test.powers[2]:=
      m2 * mmm[2] = b2 * m2 + b1 * mmm[2] + b0 * mmm[2] * mmm[-2 mod M];
    Print(test.powers[2], "\n");
    m2:= mmm[3] * mmm[3];
    test.powers[3]:=
      m2 * mmm[3] = c2 * m2 + c1 * mmm[3] + c0 * mmm[3] * mmm[-3 mod M];
    Print(test.powers[3], "\n");

    return test;
end;

test:= function()
    local   hecke,  gram,  det;
    hecke:= GenericHeckeCRG07();
    gram:= GramMatrix(hecke);
    det:= DeterminantMat(gram.gram);
    Print("det = ", det, "\n");
end;
