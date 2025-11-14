#############################################################################
##
##  H(G9)
##
Read("support.g");

HeckeCRG09:= function(params)
    local   C4Elt,  M,  N,  mmm,  c0,  c1,  c2,  c3,  null,  one,
            setter,  basicVec,  vecUnderWord,  img,  rel,  gen,  inv,
            setRow,  makeEdge,  u,  u1,  k,  z,  zs,  ts,  xs;

    # constructor
    C4Elt:= MakeC4Elts(params[1]);

    # matrices.  -1 mod 7 = 6 and -2 mod 7 = 5
    M:= 7;  N:= 48;
    mmm:= List([1..M-1], x-> []);

    # name some C4Elts
    c0:= params[1][1];  c1:= params[1][2];  c2:= params[1][3];   c3:= params[1][4];
    null:= C4Elt([0*c0, 0*c0, 0*c0, 0*c0]);    # 0
    one:= C4Elt([c0^0, 0*c0, 0*c0, 0*c0]);     # 1

    setter:= MakeSetter(M, N, null, one, mmm, params);
    basicVec:= setter.basicVec;
    vecUnderWord:= setter.vecUnderWord;
    img:= setter.img;  rel:= setter.rel;
    gen:= setter.gen;  inv:= setter.inv;
    setRow:= setter.setRow;
    makeEdge:= setter.makeEdge;

    # subgroup table
    u:= C4Elt([0*c0, c0^0, 0*c0, 0*c0]);        # u
    u1:= c0^-1 * C4Elt([-c1, -c2, -c3, c0^0]);  # u'
    for k in 6*[0..7] do
        setRow(k+1, 1, basicVec(k+1, u), img);
        setRow(k+1, -1, basicVec(k+1, u1), img);
    od;

    # spanning tree
    for k in 6*[0..7] do
        makeEdge(k+1, k+2, 2);
        makeEdge(k+2, k+3, 1);
        makeEdge(k+3, k+4, 2);
        makeEdge(k+3, k+5, 1);
        makeEdge(k+5, k+6, 2);
    od;

    # cycles
    for k in 6*[0..7] do
        setRow(k+2, 2, 0, gen);
        setRow(k+4, 2, 0, gen);
        setRow(k+6, 2, 0, gen);
        setRow(k+1, -2, 0, inv);
        setRow(k+3, -2, 0, inv);
        setRow(k+5, -2, 0, inv);
    od;

    # z*
    for k in [1..42] do
        makeEdge(k, k+6, 3);
    od;

    for k in 6*[0..6] do
        setRow(k+4, 1, [ -2, -1, -2, -1, -2, 3 ], rel);
        setRow(k+4, -1, 0, inv);
    od;

    for k in 6*[0..6] do
        setRow(k+8, -1, [ -3, 2, 1, 2, 1, 2 ], rel);
        setRow(k+11, 1, 0, gen);
    od;

    for k in 6*[0..5] do
        setRow(k+6, 1, [ -2, -1, -2, -1, -2, 3 ], rel);
    od;

    setRow(6, -1, 0, inv);
    setRow(12, -1, 0, inv);

    for k in 6*[0..4] do
        setRow(k+18, -1, [ -3, 2, 1, 2, 1, 2 ], rel);
    od;

    setRow(42, 1, 0, gen);

    setRow(5, 1, [ -2, -1, -2, -1, -2, 3 ], rel);
    setRow(46, -1, [ -3, 2, 1, 2, 1, 2 ], rel);
    setRow(46, 1, 0, gen);
    setRow(2, -1, 0, inv);

    setRow(48, -1, [ -3, 2, 1, 2, 1, 2 ], rel);
    setRow(48, 1, 0, gen);

    for k in [43..48] do
        setRow(k, 3, [ 1, 2, 1, 2, 1, 2 ], rel);
    od;

    for k in [1..6] do
        setRow(k, -3, -[ 1, 2, 1, 2, 1, 2 ], rel);
    od;

    z:= [1,2,1,2,1,2];
    zs:= [[]];
    for k in [2..8] do
        zs[k]:= Concatenation(zs[k-1], z);
    od;

    ts:= [[], [1], [1,1], [1,1,1]];
    xs:= [[], [2], [2,1], [2,1,2], [2,1,1], [2,1,1,2]];

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

GenericHeckeCRG09:= function()
    local   a0,  a1,  c0,  c1,  c2,  c3;

    ## indeterminates
    a0:= Mvp("a0");  a1:= Mvp("a1");
    c0:= Mvp("c0");  c1:= Mvp("c1");  c2:= Mvp("c2");  c3:= Mvp("c3");

    return HeckeCRG09([[c0, c1, c2, c3], [a0, a1]]);
end;

TestGenericHeckeCRG09:= function()
    local   hecke,  mmm,  M,  params,  c0,  c1,  c2,  c3,  a0,  a1,
            test,  m12,  m212,  m121,  m2;

    hecke:= GenericHeckeCRG09();

    mmm:= hecke.matgens;
    M:= Length(mmm) + 1;
    params:= hecke.params;
    c0:= params[1][1];  c1:= params[1][2];  c2:= params[1][3];  c3:= params[1][4];
    a0:= params[2][1];  a1:= params[2][2];

    test:= rec(relations:= [], powers:= []);

    Print("testing relation ... \c");
    m12:= mmm[1] * mmm[2];
    m212:= mmm[2] * m12;
    m121:= m12 * mmm[1];
    test.relations[1]:= m212 * m121 = m121 * m212;
    Print(test.relations[1], "\n");

    Print("testing power ... \c");
    m2:= mmm[1] * mmm[1];
    test.powers[1]:=
      m2 * m2 = c3 * m2 * mmm[1] + c2 * m2 + c1 * mmm[1] + c0 * mmm[1] * mmm[-1 mod M];
    Print(test.powers[1], "\n");

    Print("testing power ... \c");
    test.powers[2]:=
      mmm[2] * mmm[2] = a1 * mmm[2] + a0 * mmm[2] * mmm[-2 mod M];
    Print(test.powers[2], "\n");

    return test;
end;

test:= function()
    local   hecke,  gram,  det;
    hecke:= GenericHeckeCRG09();
    gram:= GramMatrix(hecke);
    det:= DeterminantMat(gram.gram);
    Print("det = ", det, "\n");
end;
