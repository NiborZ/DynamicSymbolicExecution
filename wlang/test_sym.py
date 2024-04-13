# The MIT License (MIT)
# Copyright (c) 2016 Arie Gurfinkel

# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:

# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

import unittest

from . import ast, sym


class TestSym (unittest.TestCase):

    def test_one(self):
        prg1 = "havoc x; assume x > 10; assert x > 15"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_two(self):
        # test if statement and AExp operations
        prg1 = "havoc x; x := 1; if x = 1 then x := x+10; if x >= 2 then x := x*2 else skip; if x <= 100 then x := 1; if x > 0 then x := 5; if x < 6 then x := x/5; if x < 100 then x := x-1"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 1)

    def test_three(self):
        # test BExp, PrintStateStmt
        prg1 = "havoc x; if true and true then x := 1; if true or false then x := x-1; if not false then x := x-1; print_state"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 1)
        if len(out) == 1:
            print(repr(out[0]))

    def test_four(self):
        # test while case 1
        prg1 = "x := 1; while x <= 5 do x := x+1; y := 5; while y < 10 do y := y+1"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 1)

    def test_five(self):
        # test while case 2
        prg1 = "x := 1; while x <= 12 do x := x+1; assert x < 10"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 0)

    def test_six(self):
        # test assume, assert
        prg1 = "havoc x; assume x>10; assert x<9"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 0)

    def test_seven_coverWhileInvariant(self):
        # test while invariant method
        prg1 = "havoc x, y; assume y >= 0; c := 0; r := x; while c < y inv r=x+c and c<=y do {r := r + 1;c := c + 1};assert r = x + y"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 1)

    def test_nine_coverWhileInvariant_invariantFailBeginning(self):
        prg1 = "havoc x, y; assume y > 2; x := 0; while x < y inv x=y do {x:=x+1};assert x=y"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 1)

    def test_ten_coverWhileInvariant_invariantFailEnd(self):
        prg1 = "havoc x, y; assume y>2 ; x := 0; while x < y inv x<=y do {x:=x+10};assert x=y"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 1)

    """
    def test_time_diverge_case(self):
        
        # It takes 18.720s
        
        prg1 = "havoc a, b, c; while a <=10 do a := a+1; while b <= 10 do b := b+1; while c <= 10 do c := c+1"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 1331)
    """

    def test_cover_unused_methods_case1(self):
        # To cover the three unused methods: pick_concerete, fork and to_smt2. They are safe to delete for this SymExec implementation
        # Not delete the unused methods because not sure whether these methods will be used in testing during marking
        # These three methods are given by Prof. Arie
        prg1 = "havoc x; assume x > 10; assert x > 15"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 1)
        sampleState = out[0]
        sampleState.to_smt2()
        sampleState.fork()
        sampleState.pick_concerete()

    def test_cover_unused_methods_case2(self):
        # To cover the three unused methods: pick_concerete, fork and to_smt2. They are safe to delete for this SymExec implementation
        # Not delete the unused methods because not sure whether these methods will be used in testing during marking
        # These three methods are given by Prof. Arie

        # Cover the pick_concerete if res != z3.sat: return None case
        import z3

        st = sym.SymState()
        var = z3.Int('x')
        st.add_pc(var == 5)
        st.add_pc(var == 3)
        st.pick_concerete()

    def test_exe1(self):
        # test exe dse
        prg1 = "havoc x;r:= 0;if x>8 then r:=x-7;if x<5 then r:=x-2"
        ast1 = ast.parse_string(prg1)
        engine = sym.EXEExec()
        st = sym.EXEState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 3)

    def test_exe2(self):
        # test exe dse
        prg1 = "havoc x;r:= 0;if x>8 then {r:=x-7;x:=x-2};if x<5 then {r:=x-2; x:=x+3}"
        ast1 = ast.parse_string(prg1)
        engine = sym.EXEExec()
        st = sym.EXEState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 3)

    def test_exe3(self):
        # test exe dse
        prg1 = "a:= 5;b:=5;if a<3 and b>3 then a:=a+5;if a>7 then b:=b+3"
        ast1 = ast.parse_string(prg1)
        engine = sym.EXEExec()
        st = sym.EXEState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 1)

    def test_exe4(self):
        # test exe dse
        prg1 = "havoc a,b;if a<3 and b>3 then a:=a+5;if a>7 then b:=b+3"
        ast1 = ast.parse_string(prg1)
        engine = sym.EXEExec()
        st = sym.EXEState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 3)

    def test_exe5(self):
        # test exe dse
        prg1 = "havoc x;r:= 0;if x>8 then r:=x-7 else x:= x*1; if x<5 then r:=x/2"
        ast1 = ast.parse_string(prg1)
        engine = sym.EXEExec()
        st = sym.EXEState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 3)

    def test_exe6(self):
        # test exe dse
        prg1 = "havoc x; if x<8 then x:=x+1 else x:=x-1"
        ast1 = ast.parse_string(prg1)
        engine = sym.EXEExec()
        st = sym.EXEState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 2)

    def test_exe_while1(self):
        # test exe while
        prg1 = "havoc x; while x < 5  do x := x + 1"
        ast1 = ast.parse_string(prg1)
        engine = sym.EXEExec()
        st = sym.EXEState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 11)

    def test_exe_while2(self):
        prg1 = "havoc x; assume x > 15; while x > 16  do x := x - 1"
        ast1 = ast.parse_string(prg1)
        engine = sym.EXEExec()
        st = sym.EXEState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 11)

    def test_exe_while3(self):
        prg1 = "x:=0; while x > 16  do x := x - 1; assert x = 1"
        ast1 = ast.parse_string(prg1)
        engine = sym.EXEExec()
        st = sym.EXEState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 0)

    def test_exe_while4(self):
        prg1 = "x:=0; while true  do x := x - 1; assert x = 1"
        ast1 = ast.parse_string(prg1)
        engine = sym.EXEExec()
        st = sym.EXEState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 0)

    def test_exe_repr(self):
        st = sym.EXEState()
        st.__repr__()

    def test_inc_one(self):
        prg1 = "havoc x; assume x > 10; assert x > 15"
        ast1 = ast.parse_string(prg1)
        engine = sym.IncExec()
        st = sym.IncState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_inc_two(self):
        # test if statement and AExp operations
        prg1 = "havoc x; x := 1; if x = 1 then x := x+10; if x >= 2 then x := x*2 else skip; if x <= 100 then x := 1; if x > 0 then x := 5; if x < 6 then x := x/5; if x < 100 then x := x-1"
        ast1 = ast.parse_string(prg1)
        engine = sym.IncExec()
        st = sym.IncState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 1)

    def test_inc_three(self):
        # test BExp, PrintStateStmt
        prg1 = "havoc x; if true and true then x := 1; if true or false then x := x-1; if not false then x := x-1; print_state"
        ast1 = ast.parse_string(prg1)
        engine = sym.IncExec()
        st = sym.IncState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 1)
        if len(out) == 1:
            print(repr(out[0]))

    def test_inc_four(self):
        # test while case 1
        prg1 = "x := 1; while x <= 5 do x := x+1; y := 5; while y < 10 do y := y+1"
        ast1 = ast.parse_string(prg1)
        engine = sym.IncExec()
        st = sym.IncState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 1)

    def test_inc_five(self):
        # test while case 2
        prg1 = "x := 1; while x <= 12 do x := x+1; assert x < 10"
        ast1 = ast.parse_string(prg1)
        engine = sym.IncExec()
        st = sym.IncState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 0)

    def test_inc_six(self):
        # test assume, assert
        prg1 = "havoc x; assume x>10; assert x<9"
        ast1 = ast.parse_string(prg1)
        engine = sym.IncExec()
        st = sym.IncState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 0)

    def test_inc_seven(self):
        # test if else
        prg1 = "havoc x; if x > 10 then x:=x+1 else x:=x-1"
        ast1 = ast.parse_string(prg1)
        engine = sym.IncExec()
        st = sym.IncState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 2)

    def test_inc_eight(self):
        # test if without else
        prg1 = "havoc x; if x > 10 then x:=x+1"
        ast1 = ast.parse_string(prg1)
        engine = sym.IncExec()
        st = sym.IncState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 2)

    def test_inc_seven_coverWhileInvariant(self):
        # test while invariant method
        prg1 = "havoc x, y; assume y >= 0; c := 0; r := x; while c < y inv r=x+c and c<=y do {r := r + 1;c := c + 1};assert r = x + y"
        ast1 = ast.parse_string(prg1)
        engine = sym.IncExec()
        st = sym.IncState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 1)

    def test_inc_nine_coverWhileInvariant_invariantFailBeginning(self):
        prg1 = "havoc x, y; assume y > 2; x := 0; while x < y inv x=y do {x:=x+1};assert x=y"
        ast1 = ast.parse_string(prg1)
        engine = sym.IncExec()
        st = sym.IncState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 1)

    def test_inc_ten_coverWhileInvariant_invariantFailEnd(self):
        prg1 = "havoc x, y; assume y>2 ; x := 0; while x < y inv x<=y do {x:=x+10};assert x=y"
        ast1 = ast.parse_string(prg1)
        engine = sym.IncExec()
        st = sym.IncState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 1)

    def test_inc_addSameActivationLiteral(self):
        st = sym.IncState()
        activationLiteral=st.get_new_activation_literal()
        st.add_activation_literal(activationLiteral)
        st.add_activation_literal(activationLiteral)

    def test_inc_inv1(self):
        prg1 = "havoc x;while x < 4 inv x < 2 do x := x / 2; assume x > 100"
        ast1 = ast.parse_string(prg1)
        engine = sym.IncExec()
        st = sym.IncState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 0)

    def test_inc_inv2(self):
        prg1 = "havoc x, y; assume y >= 0; c := 0;r := x;while c < y inv c<=y and r=x+c do{r := r + 1;c := c + 1 };assert r = x + y"
        ast1 = ast.parse_string(prg1)
        engine = sym.IncExec()
        st = sym.IncState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 1)

    def test_inc_inv3(self):
        prg1 = "havoc x;while x < 4 inv 1<0 do x := x - 2"
        ast1 = ast.parse_string(prg1)
        engine = sym.IncExec()
        st = sym.IncState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 0)

    def test_inc_inv4(self):
        prg1 = "havoc x;while x < 5 inv x<3 do x := x + 1"
        ast1 = ast.parse_string(prg1)
        engine = sym.IncExec()
        st = sym.IncState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 0)

    def test_inc_inv5(self):
        prg1 = "havoc x;assume x<2; while x>1 and x < 4 inv x< 3 do x := x + 10"
        ast1 = ast.parse_string(prg1)
        engine = sym.IncExec()
        st = sym.IncState()
        out = engine.run(ast1, st)
        self.assertEquals(len(out), 1)
