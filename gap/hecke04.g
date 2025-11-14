#############################################################################
##
##  H(G4)
##
Read("support.g");

HeckeCRG04:= function(params)
    local   C3Elt,  M,  N,  mmm,  c0,  c1,  c2,  null,  one,  setter,
            basicVec,  vecUnderWord,  img,  rel,  gen,  inv,  setRow,
            makeEdge,  u,  u1,  k,  s,  t,  z,  zs,  ts,  xs;

    # constructor
    C3Elt:= MakeC3Elts(params[1]);

    # matrices.  -1 mod 7 = 6 and -2 mod 7 = 5
    M:= 7;  N:= 8;
    mmm:= List([1..M-1], x-> []);

    # name some C3Elts
    c0:= params[1][1];  c1:= params[1][2];  c2:= params[1][3];
    null:= C3Elt([0*c0, 0*c0, 0*c0]);    # 0
    one:= C3Elt([c0^0, 0*c0, 0*c0]);     # 1

    setter:= MakeSetter(M, N, null, one, mmm, params{[1,1]});
    basicVec:= setter.basicVec;
    vecUnderWord:= setter.vecUnderWord;
    img:= setter.img;  rel:= setter.rel;
    gen:= setter.gen;  inv:= setter.inv;
    setRow:= setter.setRow;
    makeEdge:= setter.makeEdge;

    # subgroup table
    u:= C3Elt([0*c0, c0^0, 0*c0]);         # u
    u1:= c0^-1 * C3Elt([-c1, -c2, c0^0]);  # u'
    for k in [0,4] do
        setRow(k+1, 1, basicVec(k+1, u), img);
        setRow(k+1, -1, basicVec(k+1, u1), img);
        setRow(k+3, 2, basicVec(k+3, u), img);
        setRow(k+3, -2, basicVec(k+3, u1), img);
    od;

    # spanning tree(s)
    for k in [0,4] do
        makeEdge(k+1, k+2, 2);
        makeEdge(k+3, k+4, 1);
    od;

    # w*
    for k in [0..5] do
        makeEdge(k+1, k+3, 3);
    od;

    s:= 1;  t:= 2;
    for k in 2*[0..2] do
        setRow(k+2, s, [ -t, -s, 3 ], rel);
        setRow(k+3, -s, [ t, s, -3 ], rel);
        s:= 3 - s;  t:= 3 - t;
    od;

    # cycles
    s:= 1;
    for k in 2*[0..2] do
        setRow(k+4, s, 0, gen);
        setRow(k+2, -s, 0, inv);
        s:= 3 - s;
    od;

    # relations
    setRow(2, 2, [ -1, -2, 3 ], rel);
    setRow(1, -2, 0, inv);
    setRow(8, -2, [ -3, 2, 1 ], rel);
    setRow(8, 2, 0, gen);

    setRow(7, 3, [ 1, 2, 1 ], rel);
    setRow(8, 3, [ 1, 2, 1 ], rel);
    setRow(1, -3, -[ 1, 2, 1 ], rel);
    setRow(2, -3, -[ 1, 2, 1 ], rel);

    z:= [1,2,1,2,1,2];
    zs:= [[]];
    for k in [2..2] do
        zs[k]:= Concatenation(zs[k-1], z);
    od;

    ts:= [[], [1], [1,1]];
    xs:= [[], [2], [2,1,2], [2,1,2,1]];

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

GenericHeckeCRG04:= function()
    local   c0,  c1,  c2;

    ## indeterminates
    c0:= Mvp("c0");  c1:= Mvp("c1");  c2:= Mvp("c2");

    return HeckeCRG04([[c0, c1, c2]]);
end;

TestGenericHeckeCRG04:= function()
    local   hecke,  mmm,  M,  params,  c0,  c1,  c2,  test,  m12,  m2;

    hecke:= GenericHeckeCRG04();

    mmm:= hecke.matgens;
    M:= Length(mmm) + 1;
    params:= hecke.params;
    c0:= params[1][1];  c1:= params[1][2];  c2:= params[1][3];

    test:= rec(relations:= [], powers:= []);

    Print("testing relation ... \c");
    m12:= mmm[1] * mmm[2];
    test.relations[1]:= mmm[2] * m12 = m12 * mmm[1];
    Print(test.relations[1], "\n");

    Print("testing power ... \c");
    m2:= mmm[1] * mmm[1];
    test.powers[1]:=
      m2 * mmm[1] = c2 * m2 + c1 * mmm[1] + c0 * mmm[1] * mmm[-1 mod M];
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
    hecke:= GenericHeckeCRG04();
    gram:= GramMatrix(hecke);
    det:= DeterminantMat(gram.gram);
    Print("det = ", det, "\n");
end;
