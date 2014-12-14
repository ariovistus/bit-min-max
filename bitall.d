/++
 + author:         Ellery Newcomer
 + license:        BSD 
 + copyright:      Copyright (c) 2011 Ellery Newcomer All rights reserved.
 +/

/+ bsd license
Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:
1. Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.
2. Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.
3. The name of the author may not be used to endorse or promote products
derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 +/
module bitall;
/++ 
 + This module contains algorithms for finding the minimum and maximum of
 + an expression a op b, where
 + a and b range through the integer intervals [amin, amax], [bmin, bmax].
 + op is one of the binary operators:
 +    & | ^ 
 +    for either signed or unsigned arithmetic
 +
 + There should be an accompanying pdf file which describes the derivation
 + of the following algorithms. Refer to it.
 +/

import std.algorithm, std.conv, std.stdio, std.traits;
static import core.bitop;

template signed(T){
    static if(isSigned!T) alias T signed;
    else static if(is(T == ubyte)) alias byte signed;
    else static if(is(T == ushort)) alias short signed;
    else static if(is(T == uint)) alias int signed;
    else static if(is(T == ulong)) alias long signed;
}
static assert(is( signed!(ubyte) == byte));
static assert(is( signed!(byte) == byte));

template unsigned(T){
    static if(isUnsigned!T) alias T unsigned;
    else static if(is(T == byte)) alias ubyte unsigned;
    else static if(is(T == short)) alias ushort unsigned;
    else static if(is(T == int)) alias uint unsigned;
    else static if(is(T == long)) alias ulong unsigned;
}

static assert(is( unsigned!(ubyte) == ubyte));
static assert(is( unsigned!(byte) == ubyte));

private template bsr(T) if(isIntegral!T){
    static if(uint.sizeof < T.sizeof){
        static assert(T.sizeof == ulong.sizeof);
        T bsr(T x){
            uint* xsp = cast(uint*) &x;
            uint xl = xsp[0], xh = xsp[1];
            if(xh) return core.bitop.bsr(xh) + 32;
            else return core.bitop.bsr(xl);
        }
    }else static if(uint.sizeof == T.sizeof){
        alias core.bitop.bsr bsr;
    }else{
        T bsr(T x){
            return cast(T) core.bitop.bsr(x & (cast(unsigned!T) -1));
        }
    }
}

unittest{
    assert(bsr!ubyte(0x7f) == 6);
    assert(bsr!byte(0x7f) == 6);
    assert(bsr!ubyte(0x80) == 7);
    assert(bsr!byte(cast(byte)0x80) == 7);
    assert(bsr!ushort(0x7f) == 6);
    assert(bsr!short(0x7f) == 6);
    assert(bsr!uint(0x7f) == 6);
    assert(bsr!int(0x7f) == 6);
    assert(bsr!ulong(0x7f) == 6);
    assert(bsr!long(0x7f) == 6);
    assert(bsr!ulong(0x7f_ff) == 14);
    assert(bsr!long(0x7f_ff) == 14);
    assert(bsr!ulong(0x7f_ff_ff) == 22);
    assert(bsr!long(0x7f_ff_ff) == 22);
    assert(bsr!ulong(0x7f_ff_ff_ff) == 30);
    assert(bsr!long(0x7f_ff_ff_ff) == 30);
    assert(bsr!ulong(0x7f_ff_ff_ff_ff_ff_ff_ffUL) == 62);
    assert(bsr!long(0x7f_ff_ff_ff_ff_ff_ff_ffUL) == 62);
    assert(bsr!ulong(0x80_00_00_00_00_00_00_00UL) == 63);
    assert(bsr!long(0x80_00_00_00_00_00_00_00UL) == 63);
}

I hbmask(I)(I i) if(isIntegral!I){
    return cast(I) ((cast(I)1 << bsr!I(i|1))-1);
}

unittest{
    assert(hbmask(0) == 0);
    assert(hbmask(1) == 0);
    assert(hbmask(0b101011100011) 
            ==    0b011111111111);
    assert(hbmask!ubyte(0x05) == 0x03);
    assert(hbmask!ubyte(0x40) == 0x3f);
    assert(hbmask!ubyte(0x80) == 0x7f);
    assert(hbmask!ulong(0x80_00_00_00_00_00_00_00UL)
            ==          0x7f_ff_ff_ff_ff_ff_ff_ffUL);
    assert(hbmask! long(0x80_00_00_00_00_00_00_00UL)
            ==          0x7f_ff_ff_ff_ff_ff_ff_ffUL);
}

template dumb(I, string m, string op){
    static assert(m == "max" || m == "min");
    static assert(op == "&" || op == "|" || op == "^");
    enum cmp = ((m == "max") ? ">" : "<");

    I dumb(I amin, I amax, I bmin, I bmax){
        assert(amin <= amax);
        assert(bmin <= bmax);
        static if(m == "max"){
            I x = I.min;
        }else{
            I x = I.max;
        }
        for(I a = amin;; a++){
            for(I b = bmin;; b++){
                I n = mixin("cast(I)(a"~op~"b)");
                if(mixin("n"~cmp~"x")) x = n;
                if(b == bmax) break;
            }
            if(a == amax) break;
        }
        return x;
    }
}

unittest{
    assert(dumb!(uint, "max", "|")(0,8,5,6) == 14);
    assert(dumb!(uint, "min", "|")(0,8,5,6) == 5);
}

enum vst0 = q{
    I r1 = mf(amin, amax, bmin, bmax);
    I r2 = dumb!(I,m,op)(amin, amax, bmin, bmax);
    if (r1 != r2){
        writefln("Failed at a min=%s max=%s b min=%s max=%s",
                amin, amax, bmin, bmax);
        writefln("\t a min: %8b max:%8b", amin, amax);
        writefln("\t b min: %8b max:%8b", bmin, bmax);
        writefln("\t proposed: %8b", r1);
        writefln("\t verified: %8b", r2);
    }
};
enum chkassert = q{
    I r1 = mf(amin, amax, bmin, bmax);
    I r2 = dumb!(I,m,op)(amin, amax, bmin, bmax);
    assert(r1 == r2, 
            to!string(amin) ~ " " ~ 
            to!string(amax) ~ " " ~ 
            to!string(bmin) ~ " " ~ 
            to!string(bmax));
};
enum vst2 = q{
    I r1 = mf(amin, amax, bmin, bmax);
};
template iter(I, string m, string op, string visitmethod = vst0) 
    if(isIntegral!I){
    static assert(m == "max" || m == "min");
    static assert(op == "|" || op == "&" || op == "^");
    static if(m == "max"){
        static if(op == "&") alias maxand mf;
        else static if(op == "|") alias maxor mf;
        else static if(op == "^") alias maxxor mf;
    }else static if (m == "min"){
        static if(op == "&") alias minand mf;
        else static if(op == "|") alias minor mf;
        else static if(op == "^") alias minxor mf;
    }
    static if(isSigned!I){
        I maxmin0 = -32;
        I maxmax0 =  32;
        I minmin0 = -32;
    }else{
        I maxmin0 =   0;
        I maxmax0 =  64;
        I minmin0 =   0;
    }
    void outer(I maxmin = maxmin0, I maxmax = maxmax0, I minmin = minmin0)(){
        inner!(maxmin,maxmax,minmin)([0,0,0,0],0);
    }
    /// mm = [maxa,maxb,mina,minb]
    void inner(I maxmin,I maxmax,I minmin)(I[] mm, size_t i){
        if(i == 4){
            I amin =mm[2], amax = mm[0], bmin = mm[3], bmax = mm[1];
            mixin(visitmethod);
        }else if(i < 2){
            // max
            for(mm[i] = maxmin; mm[i] <= maxmax; mm[i]++){
                inner!(maxmin,maxmax,minmin)(mm, i+1);
            }
        }else{
            // min
            for(mm[i] = minmin; mm[i] <= mm[i-2]; mm[i]++){
                inner!(maxmin,maxmax,minmin)(mm,i+1);
            }
        }
    }

}

I maxand(I)(I amin, I amax, I bmin, I bmax) if(isIntegral!I)
in{
    assert(amin <= amax);
    assert(bmin <= bmax);
}body{
    static if(isSigned!I){
        // ensure I.min is what we think it is
        static assert(I.min == cast(I)((cast(I)1) << (8*I.sizeof-1)));
        // ie. highbit = 1, others = 0
        static if(is(I == byte)) static assert(byte.min == cast(byte) 0x80);

        I a0 = cast(I) (amin & ~amax &  bmax & I.min);
        I a1 = cast(I) (amin & ~amax & ~bmin & I.min);
        I b0 = cast(I) (bmin & ~bmax &  amax & I.min);
        I b1 = cast(I) (bmin & ~bmax & ~amin & I.min);
        I ab = cast(I) (amin & ~amax & bmin & ~bmax & I.min);
        if( a1 || (ab && amax < bmax)) amax = cast(I) -1;
        if( a0 || (ab && amax >=bmax)) amin = cast(I) 0;
        if( b1 || (ab && amax >=bmax)) bmax = cast(I) -1;
        if( b0 || (ab && amax < bmax)) bmin = cast(I) 0;
        return cast(I) maxand!(unsigned!I)(amin, amax, bmin, bmax);
    }else{
        I xa1 = ~amin& amax      & bmax;
        I xa0 = ~amin& amax      &~bmax;
        I xb1 =        amax&~bmin& bmax;
        I xb0 =       ~amax&~bmin& bmax;
        xa0 |= hbmask!I(xa1)&amax&~bmax;
        xb0 |= hbmask!I(xb1)&bmax&~amax;
        if(xa0 > xb0) amax |= hbmask!I(xa0);
        else bmax |= hbmask!I(xb0);
        return amax&bmax;
    }
}

unittest{
    assert(maxand!int(-1,0,-1,0) == 0);
    assert(maxand!int(-1,0,-1,1) == 1);
    assert(maxand!byte(0,8,5,6) == 6);
    iter!(byte, "max", "&", chkassert).outer!(-16,16,-16);
    iter!(ubyte, "max", "&", chkassert).outer!(0x7f,0x8f,0x7f);
    iter!(int, "max", "&", chkassert).outer!(-16,16,-16);
    iter!(uint, "max", "&", chkassert).outer!(0x7fffffff,0x8000000f,0x7fffffff);
    iter!(long, "max", "&", chkassert).outer!(-16,16,-16);
    iter!(ulong, "max", "&", chkassert).outer!(0x7fffffffffffffff,0x800000000000000f,0x7fffffffffffffff);
}

I maxor(I)(I amin, I amax, I bmin, I bmax) if(isIntegral!I)
in{
    assert(amin <= amax);
    assert(bmin <= bmax);
}body{
    static if(isSigned!I){
        // ensure I.min is what we think it is
        static assert(I.min == cast(I)((cast(I)1) << (8*I.sizeof-1)));
        // ie. highbit = 1, others = 0
        static if(is(I == byte)) static assert(byte.min == cast(byte) 0x80);

        I a1 = cast(I) ((amin & ~amax &  bmax) & I.min);
        I a0 = cast(I) ((amin & ~amax & ~bmax) & I.min);
        I b1 = cast(I) ((bmin & ~bmax &  amax) & I.min);
        I b0 = cast(I) ((bmin & ~bmax & ~amax) & I.min);
        if( a1 ) amax = -1;
        if( a0 ) amin = 0;
        if( b1 ) bmax = -1;
        if( b0 ) bmin = 0;
        return cast(I) maxor!(unsigned!I)(amin, amax, bmin, bmax);
    }else{
        I x1 = (~amin&amax& bmax)|(~bmin&bmax& amax);
        I x0 = (~amin&amax&~bmax)|(~bmin&bmax&~amax);
        x1 |= hbmask(x0)&amax&bmax;
        return amax|bmax|hbmask(x1);
    }
}

unittest{
    assert(maxor!byte(0,8,5,6) == 14);
    iter!(byte, "max", "|", chkassert).outer!(-16,16,-16);
    iter!(ubyte, "max", "|", chkassert).outer!(0x7f,0x8f,0x7f);
    iter!(int, "max", "|", chkassert).outer!(-16,16,-16);
    iter!(uint, "max", "|", chkassert).outer!(0x7fffffff,0x8000000f,0x7fffffff);
    iter!(long, "max", "|", chkassert).outer!(-16,16,-16);
    iter!(ulong, "max", "|", chkassert).outer!(0x7fffffffffffffff,0x800000000000000f,0x7fffffffffffffff);
}

I minand(I)(I amin, I amax, I bmin, I bmax) if(isIntegral!I)
in{
    assert(amin <= amax);
    assert(bmin <= bmax);
}body{
    return ~maxor!I(~amax, ~amin, ~bmax, ~bmin);
}

unittest{
    assert(minand!byte(0,8,5,6) == 0);
    iter!(byte, "min", "&", chkassert).outer!(-16,16,-16);
    iter!(ubyte, "min", "&", chkassert).outer!(0x7f,0x8f,0x7f);
    iter!(int, "min", "&", chkassert).outer!(-16,16,-16);
    iter!(uint, "min", "&", chkassert).outer!(0x7fffffff,0x8000000f,0x7fffffff);
    iter!(long, "min", "&", chkassert).outer!(-16,16,-16);
    iter!(ulong, "min", "&", chkassert).outer!(0x7fffffffffffffff,0x800000000000000f,0x7fffffffffffffff);
}

I minor(I)(I amin, I amax, I bmin, I bmax) if(isIntegral!I)
in{
    assert(amin <= amax);
    assert(bmin <= bmax);
}body{
    return ~maxand!I(~amax, ~amin, ~bmax, ~bmin);
}

unittest{
    assert(minor!byte(0,8,5,6) == 5);
    iter!(byte, "min", "|", chkassert).outer!(-16,16,-16);
    iter!(ubyte, "min", "|", chkassert).outer!(0x7f,0x8f,0x7f);
    iter!(int, "min", "|", chkassert).outer!(-16,16,-16);
    iter!(uint, "min", "|", chkassert).outer!(0x7fffffff,0x8000000f,0x7fffffff);
    iter!(long, "min", "|", chkassert).outer!(-16,16,-16);
    iter!(ulong, "min", "|", chkassert).outer!(0x7fffffffffffffff,0x800000000000000f,0x7fffffffffffffff);
}

void writeranges(I)(I amin, I amax, I bmin, I bmax){
    writefln("amin:%032b (%s)",amin,I.stringof);
    writefln("amin:%32s",amin);
    writefln("amax:%032b (%s)",amax,I.stringof);
    writefln("amax:%32s",amax);
    writefln("bmin:%032b (%s)",bmin,I.stringof);
    writefln("bmin:%32s",bmin);
    writefln("bmax:%032b (%s)",bmax,I.stringof);
    writefln("bmax:%32s",bmax);
}

I maxxor(I)(I amin, I amax, I bmin, I bmax) if(isIntegral!I)
in{
    assert(amin <= amax);
    assert(bmin <= bmax);
}body{
    static if(isSigned!I){
        // ensure I.min is what we think it is
        static assert(I.min == cast(I)((cast(I)1) << (8*I.sizeof-1)));
        // ie. highbit = 1, others = 0
        static if(is(I == byte)) static assert(byte.min == cast(byte) 0x80);

        debug{
            writeranges(amin,amax,bmin,bmax);
        }
        I a0 = cast(I)( amin &~amax & ~bmin & I.min);
        I a1 = cast(I)( amin &~amax &  bmax & I.min);
        I b0 = cast(I)( bmin &~bmax & ~amin & I.min);
        I b1 = cast(I)( bmin &~bmax &  amax & I.min);
        I ab = cast(I)( amin &~amax & bmin &~bmax & I.min);
        if( ab ){
            return max(
                    maxxor!(unsigned!I)(amin,cast(I) -1, bmin, cast(I) -1),
                    maxxor!(unsigned!I)(0,amax, 0, bmax));
        }
        if( a0 ) amin = cast(I) 0;
        if( a1 ) amax = cast(I) -1;
        if( b0 ) bmin = cast(I) 0;
        if( b1 ) bmax = cast(I) -1;
        debug{
            writeranges(amin,amax,bmin,bmax);
        }
        return maxxor!(unsigned!I)(amin,amax,bmin,bmax);
    }else{
        I xa00 = (~amin& amax&~bmin&~bmax);
        I xb00 = (~amin&~amax&~bmin& bmax);
        I xa11 = (~amin& amax& bmin& bmax);
        I xb11 = ( amin& amax&~bmin& bmax);
        I xab  = (~amin& amax&~bmin& bmax);
        I xia  = xa00 | (hbmask(xb00)&~amin& amax&~bmax) 
                      | (hbmask(xa11)&~amin&~bmin&~bmax);
        I xib  = xb00 | (hbmask(xa00)&~bmin& bmax&~amax) 
                      | (hbmask(xb11)&~bmin&~amin&~amax);
        I xja  = xa11 | (hbmask(xa00)& amax& bmin& bmax) 
                      | (hbmask(xb11)&~amin& amax& bmin);
        I xjb  = xb11 | (hbmask(xb00)& bmax& amin& amax) 
                      | (hbmask(xa11)&~bmin& bmax& amin);
        I xk   = xab  | (hbmask(xia )& amax&~bmin& bmax)
                      | (hbmask(xib )& bmax&~amin& amax)
                      | (hbmask(xja )&~amin& amax&~bmin)
                      | (hbmask(xjb )&~bmin& bmax&~amin);
        amin &= ~hbmask(xia);
        bmax |=  hbmask(xjb);
        bmin &= ~hbmask(xib);
        amax |=  hbmask(xja);
        return (amin ^ bmax) | (amax ^ bmin) | hbmask(xk);
    }
}

unittest{
    assert(maxxor!byte(0,8,5,6) == 14);
    assert(maxxor!int(0,8,5,6) == 14);
    assert(maxxor!uint(0,8,5,6) == 14);
    assert(maxxor!long(0,8,5,6) == 14);
    assert(maxxor!long(-1,0,-1,1) == 1);
    iter!(byte, "max", "^", chkassert).outer!(-16,16,-16);
    iter!(ubyte, "max", "^", chkassert).outer!(0x7f,0x8f,0x7f);
    iter!(int, "max", "^", chkassert).outer!(-16,16,-16);
    iter!(uint, "max", "^", chkassert).outer!(0x7fffffff,0x8000000f,0x7fffffff);
    iter!(long, "max", "^", chkassert).outer!(-16,16,-16);
    iter!(ulong, "max", "^", chkassert).outer!(0x7fffffffffffffff,0x800000000000000f,0x7fffffffffffffff);
}

I minxor(I)(I amin, I amax, I bmin, I bmax) if(isIntegral!I)
in{
    assert(amin <= amax);
    assert(bmin <= bmax);
}body{
    static if(isSigned!I){
        // ensure I.min is what we think it is
        static assert(I.min == cast(I)((cast(I)1) << (8*I.sizeof-1)));
        // ie. highbit = 1, others = 0
        static if(is(I == byte)) static assert(byte.min == cast(byte) 0x80);

        /+
        I a0 = cast(I)(amin & ~amax &  bmax & I.min);
        I a1 = cast(I)(amin & ~amax & ~bmin & I.min);
        I b0 = cast(I)(bmin & ~bmax &  amax & I.min);
        I b1 = cast(I)(bmin & ~bmax & ~amin & I.min);
        I ab = cast(I)(amin & ~amax &  bmin & ~bmax & I.min);
        +/
        if( amin < 0 && amax >= 0 && bmin < 0 && bmax >= 0 ){
            return min( minxor!(unsigned!I)(0,amax,bmin, cast(I)-1),
                        minxor!(unsigned!I)(amin,cast(I)-1,0,bmax));
        }
        if( amin < 0 && amax >= 0 && bmax <  0) amin =  0;
        if( amin < 0 && amax >= 0 && bmin >= 0) amax = -1;
        if( bmin < 0 && bmax >= 0 && amax <  0) bmin =  0;
        if( bmin < 0 && bmax >= 0 && amin >= 0) bmax = -1;
        return minxor!(unsigned!I)(amin,amax,bmin,bmax);
    }else{
        I xa00 = (~amin& amax&~bmin&~bmax);
        I xb00 = (~amin&~amax&~bmin& bmax);
        I xa11 = (~amin& amax& bmin& bmax);
        I xb11 = ( amin& amax&~bmin& bmax);
        I xab  = (~amin& amax&~bmin& bmax);
        I xa00a11 = (hbmask(xa00)&~amin&       bmin& bmax);
        I xa00b11 = (hbmask(xa00)& amin&      ~bmin& bmax);
        I xb00a11 = (hbmask(xb00)&~amin& amax& bmin      );
        I xb00b11 = (hbmask(xb00)& amin& amax&~bmin      );
        I xa11a00 = (hbmask(xa11)      & amax&~bmin&~bmax);
        I xb11a00 = (hbmask(xb11)&~amin& amax      &~bmax);
        I xa11b00 = (hbmask(xa11)      &~amax&~bmin& bmax);
        I xb11b00 = (hbmask(xb11)&~amin&~amax      & bmax);
        I xia  = xa11 | xa00a11 | xb00a11;
        I xib  = xb11 | xa00b11 | xb00b11;
        I xja  = xa00 | xa11a00 | xb11a00; 
        I xjb  = xb00 | xa11b00 | xb11b00;

        I xk   = xab  | (hbmask(xa00)&~amin&      ~bmin& bmax)
                      | (hbmask(xb00)&~amin& amax&~bmin)
                      | (hbmask(xa11)      & amax&~bmin& bmax)
                      | (hbmask(xb11)&~amin& amax      & bmax)

                      | (hbmask(xa00a11|xa11a00)            &~bmin& bmax)
                      | (hbmask(xa00b11|xb11a00)&~amin            & bmax)
                      | (hbmask(xb00a11|xa11b00)      & amax&~bmin      )
                      | (hbmask(xb00b11|xb11b00)&~amin& amax            );

        if (xia > xib){
            amin &= ~hbmask(xia);
        }else{
            bmin &= ~hbmask(xib);
        }
        if (xja > xjb){
            amax |=  hbmask(xja);
        }else {
            bmax |=  hbmask(xjb);
        }
        return (amin ^ bmin) & (amax ^ bmax) & ~hbmask(xk);
    }
}

unittest{
    assert(minxor!long(0,0,-32,0) == -32);
    iter!(byte, "min", "^", chkassert).outer!(-16,16,-16);
    iter!(ubyte, "min", "^", chkassert).outer!(0x7f,0x8f,0x7f);
    iter!(int, "min", "^", chkassert).outer!(-16,16,-16);
    iter!(uint, "min", "^", chkassert).outer!(0x7fffffff,0x8000000f,0x7fffffff);
    iter!(long, "min", "^", chkassert).outer!(-16,16,-16);
    iter!(ulong, "min", "^", chkassert).outer!(0x7fffffffffffffff,0x800000000000000f,0x7fffffffffffffff);
}

void main(){
    //iter!(uint,"max","&").outer();
    //iter!(ubyte,"max","&").outer!(0x7f,0x8f,0x7f);
    //iter!(ubyte,"max","|").outer!(0x7f,0x8f,0x7f);
    //iter!(uint,"max","|").outer();
    //iter!(int,"max","|").outer();
    //iter!(uint,"min","&").outer;
    //iter!(byte,"min","|").outer();
    //iter!(int,"max","^").outer();
    //iter!(int,"min","^",vst1).outer!(-32,64,-32);
    //iter!(int,"max","&",vst1).outer!(-32,32,-32);
    //iter!(short,"min","^").outer;
}
