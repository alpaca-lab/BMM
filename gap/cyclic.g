#############################################################################
##
##  C3Elts
##

#  a C3 elt is a triple of polynomials in c, b, a
#  corresponding to the coefficients of a linear combination
#  of u^0, u^1 and u^2
#  addition is componentwise
#  multiplication distributive, where u^3 = a u^2 + b u + c
#  inversion:  c u' = u^2 - a u - b.

MakeC3Elts:= function(params)
    local   c,  b,  a,  C3EltOps,  C3Elt,  IsC3Elt,  p,  i,  j,  l;

    c:= params[1];  b:= params[2];  a:= params[3];

    # operations record
    C3EltOps:= OperationsRecord("C3EltsOps");

    # constructor
    C3Elt:= function(list)
        return rec(list:= list, isC3Elt:= true, operations:= C3EltOps);
    end;

    # type check
    IsC3Elt:= function(obj)
        return IsRec(obj) and IsBound(obj.isC3Elt) and obj.isC3Elt = true;
    end;

    # how to print
    C3EltOps.Print:= function(self)
        if self.list = 0*self.list then
            Print(self.list[1]);
        else
            if self.list[1] <> 0 * self.list[1] then
                Print(self.list[1], "");
            fi;
            if self.list[2] <> 0 * self.list[2] then
                Print("+(", self.list[2], ")*u");
            fi;
            if self.list[3] <> 0 * self.list[3] then
                Print("+(", self.list[3], ")*u^2");
            fi;
        fi;
    end;

    # sum
    C3EltOps.\+:= function(l, r)
        return C3Elt(l.list + r.list);
    end;

    # product
    C3EltOps.\*:= function(l, r)
        local   p,  i,  j;

        if not IsC3Elt(l) then
            return C3Elt(l * r.list);
        fi;

        if IsList(r) then
            return List(r, x -> l * x);
        fi;

        p:= 0 * c *  [2..Sum(List([l, r]), x-> Length(x.list))];
        for i in [0..Length(l.list)-1] do
            for j in [0..Length(r.list)-1] do
                p[i+j+1]:= p[i+j+1] + l.list[i+1] * r.list[j+1];
            od;
        od;
        for l in Reversed([4..Length(p)]) do   # u^3 = a u^2 + b u + c
            p[l-1]:= p[l-1] + a * p[l];
            p[l-2]:= p[l-2] + b * p[l];
            p[l-3]:= p[l-3] + c * p[l];
            Unbind(p[l]);
        od;
        return C3Elt(p);
    end;

    return C3Elt;
end;

#############################################################################
##
##  C4Elts
##

#  a C4 elt is a quadruple of polynomials in a, b, c, d
#  corresponding to the coefficients of a linear combination
#  of s^0, s^1, s^2 and s^3
#  addition is componentwise
#  multiplication distributive, where s^4 = a s^3 + b s^2 + c s + d
#  inversion:  d s' = s^3 - a s^2 - b s - c.

MakeC4Elts:= function(params)
    local   d,  c,  b,  a,  C4EltOps,  C4Elt,  IsC4Elt,  o,  p,  i,
            j,  l;

    d:= params[1];  c:= params[2];  b:= params[3];  a:= params[4];

    # operations record
    C4EltOps:= OperationsRecord("C4EltsOps");

    # constructor
    C4Elt:= function(list)
        return rec(list:= list, isC4Elt:= true, operations:= C4EltOps);
    end;

    # type check
    IsC4Elt:= function(obj)
        return IsRec(obj) and IsBound(obj.isC4Elt) and obj.isC4Elt = true;
    end;

    # how to print
    C4EltOps.Print:= function(self)
        #    Print("C4Elt(", self.list, ")");
        if self.list = 0*self.list then
            Print(self.list[1]);
        else
            if self.list[1] <> 0 * self.list[1] then
                Print(self.list[1], "");
            fi;
            if self.list[2] <> 0 * self.list[2] then
                Print("+(", self.list[2], ")*s");
            fi;
            if self.list[3] <> 0 * self.list[3] then
                Print("+(", self.list[3], ")*s^2");
            fi;
            if self.list[4] <> 0 * self.list[4] then
                Print("+(", self.list[4], ")*s^3");
            fi;
        fi;
    end;

    # sum
    C4EltOps.\+:= function(l, r)
        return C4Elt(l.list + r.list);
    end;

    # product
    C4EltOps.\*:= function(l, r)
        local   o,  p,  i,  j;

        if not IsC4Elt(l) then
            return C4Elt(l * r.list);
        fi;

        if IsList(r) then
            return List(r, x -> l * x);
        fi;

        o:= 0 * d;
        p:= o * [2..Length(l.list)+Length(r.list)];
        for i in [0..Length(l.list)-1] do
            if l.list[i+1] <> o then
                for j in [0..Length(r.list)-1] do
                    if r.list[j+1] <> o then
                        p[i+j+1]:= p[i+j+1] + l.list[i+1] * r.list[j+1];
                    fi;
                od;
            fi;
        od;
        for l in Reversed([5..Length(p)]) do   # s^4 = a s^3 + b s^2 + c s + d
            if p[l] <> o then
                p[l-1]:= p[l-1] + a * p[l];
                p[l-2]:= p[l-2] + b * p[l];
                p[l-3]:= p[l-3] + c * p[l];
                p[l-4]:= p[l-4] + d * p[l];
            fi;
            Unbind(p[l]);
        od;
        return C4Elt(p);
    end;

    return C4Elt;
end;
