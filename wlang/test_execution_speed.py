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

TEST_LOOP_TIME=50

class TestSym (unittest.TestCase):
    
    def test_simple_one(self):
        for i in range(TEST_LOOP_TIME):
            prg1 = "havoc x; assume x > 10; assert x > 15"
            ast1 = ast.parse_string(prg1)
            engine = sym.SymExec()
            st = sym.SymState()
            out = [s for s in engine.run(ast1, st)]
            self.assertEquals(len(out), 1)

    def test_simple_two(self):
        # test if statement and AExp operations
        for i in range(TEST_LOOP_TIME):
            prg1 = "havoc x; x := 1; if x = 1 then x := x+10; if x >= 2 then x := x*2 else skip; if x <= 100 then x := 1; if x > 0 then x := 5; if x < 6 then x := x/5; if x < 100 then x := x-1"
            ast1 = ast.parse_string(prg1)
            engine = sym.SymExec()
            st = sym.SymState()
            out = engine.run(ast1, st)
            self.assertEquals(len(out), 1)

    def test_simple_three(self):
        # test BExp, PrintStateStmt
        for i in range(TEST_LOOP_TIME):
            prg1 = "havoc x; if true and true then x := 1; if true or false then x := x-1; if not false then x := x-1; print_state"
            ast1 = ast.parse_string(prg1)
            engine = sym.SymExec()
            st = sym.SymState()
            out = engine.run(ast1, st)
            self.assertEquals(len(out), 1)
            if len(out) == 1:
                print(repr(out[0]))

    def test_simple_four(self):
        # test while case 1
        for i in range(TEST_LOOP_TIME):
            prg1 = "x := 1; while x <= 5 do x := x+1; y := 5; while y < 10 do y := y+1"
            ast1 = ast.parse_string(prg1)
            engine = sym.SymExec()
            st = sym.SymState()
            out = engine.run(ast1, st)
            self.assertEquals(len(out), 1)
    

    """
    def test_whilebag_1(self):
        # test while invariant method
        for i in range(TEST_LOOP_TIME):
            prg1 = "havoc x, y; assume y >= 0; c := 0; r := x; while c < y inv r=x+c and c<=y do {r := r + 1;c := c + 1};assert r = x + y"
            ast1 = ast.parse_string(prg1)
            engine = sym.SymExec()
            st = sym.SymState()
            out = engine.run(ast1, st)
            self.assertEquals(len(out), 1)

    def test_whilebag_2(self):
        for i in range(TEST_LOOP_TIME):
            prg1 = "havoc x, y; assume y > 2; x := 0; while x < y inv x=y do {x:=x+1};assert x=y"
            ast1 = ast.parse_string(prg1)
            engine = sym.SymExec()
            st = sym.SymState()
            out = engine.run(ast1, st)
            self.assertEquals(len(out), 1)

    def test_whilebag_3(self):
        for i in range(TEST_LOOP_TIME):
            prg1 = "havoc x, y; assume y>2 ; x := 0; while x < y inv x<=y do {x:=x+10};assert x=y"
            ast1 = ast.parse_string(prg1)
            engine = sym.SymExec()
            st = sym.SymState()
            out = engine.run(ast1, st)
            self.assertEquals(len(out), 1)
    
    def test_whilebag_4(self):
        for i in range(TEST_LOOP_TIME):
            prg1 = "havoc x;while x < 4 inv x < 2 do x := x / 2; assume x > 100"
            ast1 = ast.parse_string(prg1)
            engine = sym.SymExec()
            st = sym.SymState()
            out = engine.run(ast1, st)
            self.assertEquals(len(out), 0)
    """
        
    """
    def test_simple_inc_one(self):
        for i in range(TEST_LOOP_TIME):
            prg1 = "havoc x; assume x > 10; assert x > 15"
            ast1 = ast.parse_string(prg1)
            engine = sym.IncExec()
            st = sym.IncState()
            out = [s for s in engine.run(ast1, st)]
            self.assertEquals(len(out), 1)

    def test_simple_inc_two(self):
        # test if statement and AExp operations
        for i in range(TEST_LOOP_TIME):
            prg1 = "havoc x; x := 1; if x = 1 then x := x+10; if x >= 2 then x := x*2 else skip; if x <= 100 then x := 1; if x > 0 then x := 5; if x < 6 then x := x/5; if x < 100 then x := x-1"
            ast1 = ast.parse_string(prg1)
            engine = sym.IncExec()
            st = sym.IncState()
            out = engine.run(ast1, st)
            self.assertEquals(len(out), 1)

    def test_simple_inc_three(self):
        # test BExp, PrintStateStmt
        for i in range(TEST_LOOP_TIME):
            prg1 = "havoc x; if true and true then x := 1; if true or false then x := x-1; if not false then x := x-1; print_state"
            ast1 = ast.parse_string(prg1)
            engine = sym.IncExec()
            st = sym.IncState()
            out = engine.run(ast1, st)
            self.assertEquals(len(out), 1)
            if len(out) == 1:
                print(repr(out[0]))

    def test_simple_inc_four(self):
        # test while case 1
        for i in range(TEST_LOOP_TIME):
            prg1 = "x := 1; while x <= 5 do x := x+1; y := 5; while y < 10 do y := y+1"
            ast1 = ast.parse_string(prg1)
            engine = sym.IncExec()
            st = sym.IncState()
            out = engine.run(ast1, st)
            self.assertEquals(len(out), 1)
    """

    """
    def test_inc_whilebag_1(self):
        # test while invariant method
        for i in range(TEST_LOOP_TIME):
            prg1 = "havoc x, y; assume y >= 0; c := 0; r := x; while c < y inv r=x+c and c<=y do {r := r + 1;c := c + 1};assert r = x + y"
            ast1 = ast.parse_string(prg1)
            engine = sym.IncExec()
            st = sym.IncState()
            out = engine.run(ast1, st)
            self.assertEquals(len(out), 1)

    def test_inc_whilebag_2(self):
        for i in range(TEST_LOOP_TIME):
            prg1 = "havoc x, y; assume y > 2; x := 0; while x < y inv x=y do {x:=x+1};assert x=y"
            ast1 = ast.parse_string(prg1)
            engine = sym.IncExec()
            st = sym.IncState()
            out = engine.run(ast1, st)
            self.assertEquals(len(out), 1)

    def test_inc_whilebag_3(self):
        for i in range(TEST_LOOP_TIME):
            prg1 = "havoc x, y; assume y>2 ; x := 0; while x < y inv x<=y do {x:=x+10};assert x=y"
            ast1 = ast.parse_string(prg1)
            engine = sym.IncExec()
            st = sym.IncState()
            out = engine.run(ast1, st)
            self.assertEquals(len(out), 1)
    
    def test_inc_whilebag_4(self):
        for i in range(TEST_LOOP_TIME):
            prg1 = "havoc x;while x < 4 inv x < 2 do x := x / 2; assume x > 100"
            ast1 = ast.parse_string(prg1)
            engine = sym.IncExec()
            st = sym.IncState()
            out = engine.run(ast1, st)
            self.assertEquals(len(out), 0)
    """