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

import sys

import io
import z3

from . import ast, int, undef_visitor
import copy
from functools import reduce

MAX_WHILE_DEPTH = 10


class SymState(object):
    def __init__(self, solver=None):
        # environment mapping variables to symbolic constants
        self.env = dict()
        # path condition
        self.path = list()
        self._solver = solver
        if self._solver is None:
            self._solver = z3.Solver()

        # true if this is an error state
        self._is_error = False

    def add_pc(self, *exp):
        """Add constraints to the path condition"""
        self.path.extend(exp)
        self._solver.append(exp)

    def is_error(self):
        return self._is_error

    def mk_error(self):
        self._is_error = True

    def is_empty(self):
        """Check whether the current symbolic state has any concrete states"""
        res = self._solver.check()
        return res == z3.unsat

    # Not used method, safe to delete
    def pick_concerete(self):
        """Pick a concrete state consistent with the symbolic state.
           Return None if no such state exists"""
        res = self._solver.check()
        if res != z3.sat:
            return None
        model = self._solver.model()
        st = int.State()
        for (k, v) in self.env.items():
            st.env[k] = model.eval(v)
        return st

    # Not used method, safe to delete
    def fork(self):
        """Fork the current state into two identical states that can evolve separately"""
        child = SymState()
        child.env = dict(self.env)
        child.add_pc(*self.path)

        return (self, child)

    def __repr__(self):
        return str(self)

    # Not used method, safe to delete
    def to_smt2(self):
        """Returns the current state as an SMT-LIB2 benchmark"""
        return self._solver.to_smt2()

    def __str__(self):
        buf = io.StringIO()
        for k, v in self.env.items():
            buf.write(str(k))
            buf.write(': ')
            buf.write(str(v))
            buf.write('\n')
        buf.write('pc: ')
        buf.write(str(self.path))
        buf.write('\n')

        return buf.getvalue()


class SymExec(ast.AstVisitor):
    def __init__(self):
        self.whileDepthCounter = 0

    def run(self, ast, state):
        # set things up and
        # call self.visit (ast, state=state)
        return self.visit(ast, state=state)

    def visit_IntVar(self, node, *args, **kwargs):
        return kwargs['state'].env[node.name]

    def visit_BoolConst(self, node, *args, **kwargs):
        return z3.BoolVal(node.val)

    def visit_IntConst(self, node, *args, **kwargs):
        return z3.IntVal(node.val)

    def visit_RelExp(self, node, *args, **kwargs):
        lhs = self.visit(node.arg(0), *args, **kwargs)
        rhs = self.visit(node.arg(1), *args, **kwargs)
        if node.op == "<=":
            return lhs <= rhs
        if node.op == "<":
            return lhs < rhs
        if node.op == "=":
            return lhs == rhs
        if node.op == ">=":
            return lhs >= rhs
        if node.op == ">":
            return lhs > rhs

        # assert False

    def visit_BExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]

        if node.op == "not":
            assert node.is_unary()
            assert len(kids) == 1
            return z3.Not(kids[0])

        fn = None
        base = None
        if node.op == "and":
            def fn(x, y): return z3.And(x, y)
            base = z3.BoolVal(True)
        elif node.op == "or":
            def fn(x, y): return z3.Or(x, y)
            base = z3.BoolVal(False)

        assert fn is not None
        return reduce(fn, kids, base)

    def visit_AExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]

        fn = None

        if node.op == "+":
            def fn(x, y): return x + y

        elif node.op == "-":
            def fn(x, y): return x - y

        elif node.op == "*":
            def fn(x, y): return x * y

        elif node.op == "/":
            def fn(x, y): return x / y

        assert fn is not None
        return reduce(fn, kids)

    def visit_SkipStmt(self, node, *args, **kwargs):
        st = kwargs['state']
        return st

    def visit_PrintStateStmt(self, node, *args, **kwargs):
        st = kwargs['state']
        print(st)
        return st

    def visit_AsgnStmt(self, node, *args, **kwargs):
        st = kwargs['state']

        # Get value
        assignValue = self.visit(node.rhs, *args, **kwargs)

        # Assign value again in case if it's not declared by havoc before
        # Add the value to z3 constraint
        # Must use FreshInt, overwise when later assigns value again it will fail
        newVar = z3.FreshInt(node.lhs.name)
        st.env[node.lhs.name] = newVar
        st.add_pc(newVar == assignValue)

        return st

    def visit_IfStmt(self, node, *args, **kwargs):

        cond = self.visit(node.cond, *args, **kwargs)

        # Create two potential states here, if statement being True and statement being False
        # trueState enters then block, falseState enters else block
        trueStateKwargs = copy.deepcopy(kwargs)
        falseStateKwargs = copy.deepcopy(kwargs)

        # Add conditions
        trueStateKwargs['state'].add_pc(cond)
        falseStateKwargs['state'].add_pc(z3.Not(cond))

        newStates = []

        # Enter then state
        trueNewStates = self.visit(node.then_stmt, *args, **trueStateKwargs)
        trueNewStates = self._object_tolist(trueNewStates)
        newStates = newStates+trueNewStates

        # Enter else state
        if node.has_else():
            falseNewStates = self.visit(
                node.else_stmt, *args, **falseStateKwargs)
            falseNewStates = self._object_tolist(falseNewStates)
            newStates = newStates+falseNewStates
        else:
            newStates = newStates+[falseStateKwargs['state']]

        return newStates

    def visit_WhileStmt(self, node, *args, **kwargs):
        if node.inv:
            return self.visit_WhileStmt_Invariant(node, *args, **kwargs)
        else:
            return self.visit_WhileStmt_NoInvariant(node, *args, **kwargs)

    def visit_WhileStmt_NoInvariant(self, node, *args, **kwargs):

        cond = self.visit(node.cond, *args, **kwargs)

        # Create two potential states here,  condition being True and condition being False
        # trueState enters inside block, falseState exists
        trueStateKwargs = copy.deepcopy(kwargs)
        falseStateKwargs = copy.deepcopy(kwargs)

        # Add conditions
        trueStateKwargs['state'].add_pc(cond)
        falseStateKwargs['state'].add_pc(z3.Not(cond))

        self.whileDepthCounter = self.whileDepthCounter+1
        newStates = []

        # Enter true condition
        if self.whileDepthCounter <= MAX_WHILE_DEPTH:
            bodyStates = self.visit(node.body, *args, **trueStateKwargs)
            bodyStates = self._object_tolist(bodyStates)
            for state in bodyStates:
                if not state.is_empty():
                    freshStateKwargs = copy.deepcopy(kwargs)
                    freshStateKwargs['state'] = state
                    newGenStates = self.visit(node, *args, **freshStateKwargs)
                    newGenStates = self._object_tolist(newGenStates)
                    newStates = newStates+newGenStates
        else:
            self.whileDepthCounter = 0

        # Reset loop counter if no feasible path is possible
        if len(newStates) == 0:
            self.whileDepthCounter = 0

        # Enter false condition
        newStates = newStates+[falseStateKwargs['state']]

        return newStates

    def visit_WhileStmt_Invariant(self, node, *args, **kwargs):

        # assert invariant first
        inv = self.visit(node.inv, *args, **kwargs)
        assertInvariantStateKwargs = copy.deepcopy(kwargs)

        # report assertion failure at initiation
        assertInvariantStateKwargs['state'].add_pc(inv)
        if not kwargs['state'].is_empty() and assertInvariantStateKwargs['state'].is_empty():
            print("Invariant assertion failed before the loop entered ")

        # transit to arbitrary state
        underVisitor = undef_visitor.UndefVisitor()
        underVisitor.check(node.body)
        definedVariables = underVisitor.get_defs()
        arbitraryNewStateKwargs = copy.deepcopy(kwargs)

        # havoc
        for v in definedVariables:
            arbitraryNewStateKwargs['state'].env[v.name] = z3.FreshInt(v.name)

        # assume inv, add inv into path condition
        inv = self.visit(node.inv, *args, **arbitraryNewStateKwargs)
        arbitraryNewStateKwargs['state'].add_pc(inv)

        # now enters the loop

        cond = self.visit(node.cond, *args, **arbitraryNewStateKwargs)

        # Create two potential states here,  condition being True and condition being False
        # trueState enters inside block, falseState exists
        trueStateKwargs = copy.deepcopy(arbitraryNewStateKwargs)
        falseStateKwargs = copy.deepcopy(arbitraryNewStateKwargs)

        # Add conditions
        trueStateKwargs['state'].add_pc(cond)
        falseStateKwargs['state'].add_pc(z3.Not(cond))

        newStates = []

        # Enter true condition
        bodyStates = self.visit(node.body, *args, **trueStateKwargs)
        bodyStates = self._object_tolist(bodyStates)
        for state in bodyStates:
            if not state.is_empty():
                # If inv && b is true, then inv is inductive, no need to continue https://campuswire.com/c/G2011444A/feed/193
                # Invariant should hold at the end of execution
                freshStateKwargs = copy.deepcopy(trueStateKwargs)
                freshStateKwargs['state'] = state
                freshInv = self.visit(node.inv, *args, **freshStateKwargs)
                state.add_pc(freshInv)
                # if state.is_empty():
                #    print("Invariant assertion failed at the loop ends")

        # Enter false condition
        newStates = newStates+[falseStateKwargs['state']]

        return newStates

    def visit_AssertStmt(self, node, *args, **kwargs):
        # Don't forget to print an error message if an assertion might be violated
        st = kwargs['state']

        cond = self.visit(node.cond, *args, **kwargs)

        # Create two potential states here, one being True and one being False
        trueState = copy.deepcopy(st)
        falseState = copy.deepcopy(st)

        # Add conditions
        trueState.add_pc(cond)
        falseState.add_pc(z3.Not(cond))

        # Print error message when the value of states can enter the false assertion state
        if not falseState.is_empty():
            falseState.mk_error()
            print(
                "The condition for assertion here may be violated (entering assertion false): "+str(trueState))

        return [trueState, falseState]

    def visit_AssumeStmt(self, node, *args, **kwargs):
        st = kwargs['state']
        cond = self.visit(node.cond, *args, **kwargs)
        st.add_pc(cond)
        return st

    def visit_HavocStmt(self, node, *args, **kwargs):
        st = kwargs['state']
        for v in node.vars:
            # Must use FreshInt, overwise when later assigns value again it will fail
            st.env[v.name] = z3.FreshInt(v.name)
        return st

    def _object_tolist(self, object):
        if not isinstance(object, list):
            return [object]
        return object

    def visit_StmtList(self, node, *args, **kwargs):
        st = kwargs['state']
        # print("Initial state is: "+str(st))
        # print("Initial node is: "+str(node.stmts))

        trackStates = []
        trackStates.append(st)

        for stmt in node.stmts:
            # explore executing new stmt for every previous state
            trackNewGenStates = []
            for state in trackStates:
                freshKwargs = copy.deepcopy(kwargs)
                freshKwargs['state'] = state
                newStates = self.visit(stmt, *args, **freshKwargs)
                newStates = self._object_tolist(newStates)
                trackNewGenStates = trackNewGenStates+newStates

            validState = []
            for state in trackNewGenStates:
                if state.is_empty():
                    print("infeasible state: "+str(state))
                elif state.is_error():
                    print(
                        "this is an error state, optionally filter it out according to https://campuswire.com/c/G2011444A/feed/145: "+str(state))
                else:
                    validState.append(state)

            trackStates = validState

        return trackStates


class ConState(SymState):
    def __init__(self, solver=None):
        super().__init__(solver)
        self.conEnv = {}

    def is_con_empty(self):
        fake_st = self.fork()[1]
        fake_path = self.path[:]
        new_fake_path = []
        solver = z3.Solver()
        for path in fake_path:
            for k, v in fake_st.env.items():
                if v not in path.children():
                    continue
                new_path = z3.substitute(path, (v, z3.IntVal(self.conEnv[k])))
                new_fake_path.append(new_path)
                solver.append(new_path)
        is_empty = solver.check() == z3.unsat
        return is_empty

    def add_concrete_var(self, name, conValue=None):
        if conValue is None:
            if name not in self.conEnv:
                self.conEnv[name] = 1
        else:
            if type(conValue) == z3.IntNumRef:
                self.conEnv[name] = conValue.as_long()
            else:
                self.conEnv[name] = conValue


class ConExec(SymExec):
    def visit_AExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]
        # Calculate concrete result
        conKids = kids[:]
        inverseDict = {kwargs['state'].env[k]: k for k in kwargs['state'].env}
        for i in range(len(conKids)):
            if type(kids[i]) != z3.IntNumRef:
                key = inverseDict[kids[i]]
                conKids[i] = kwargs['state'].conEnv[key]
            if type(conKids[i]) == z3.IntNumRef:
                # Convert concrete result to int number
                conKids[i] = conKids[i].as_long()
        fn = None

        if node.op == "+":
            def fn(x, y): return x + y

        elif node.op == "-":
            def fn(x, y): return x - y

        elif node.op == "*":
            def fn(x, y): return x * y

        elif node.op == "/":
            def fn(x, y): return x / y

        assert fn is not None
        return reduce(fn, conKids)
    pass


class EXEState(SymState):
    def __init__(self):
        self.symState = SymState()
        self.conState = ConState()
        self._lastFeasibleState = []
        self.curStIndex = 0

    def update_concrete_value(self):
        res = self.conState._solver.check()
        if res != z3.sat:
            return
        model = self.conState._solver.model()
        st = int.State()
        for (k, v) in self.conState.env.items():
            if type(model.eval(v)) != z3.IntNumRef and k in self.conState.conEnv:
                # If the model value is not an integer, use the previous concrete value
                st.env[k] = self.conState.conEnv[k]
            else:
                st.env[k] = model.eval(v).as_long()
        self.conState.conEnv = st.env

    def add_later_explore_state(self, newStates):
        self._lastFeasibleState.extend(newStates)
        return

    def get_later_state(self):
        s_list = self._lastFeasibleState[:]
        self._lastFeasibleState = []
        return s_list

    def add_pc(self, *exp):
        self.symState.add_pc(*exp)
        self.conState.add_pc(*exp)

    def is_empty(self):
        return self.symState.is_empty()

    def is_con_empty(self):
        return self.conState.is_con_empty()

    def is_error(self):
        return self.symState.is_error()

    def mk_error(self):
        return self.symState.mk_error()

    def __repr__(self):
        return "SYM: " + str(self.symState)+"\nCON: "+str(self.conState.conEnv)

    def __str__(self):
        return "SYM: " + str(self.symState)+"\nCON: "+str(self.conState.conEnv)


class EXEExec(ConExec):
    def visit_AExp(self, node, *args, **kwargs):
        st = kwargs['state']
        if type(st) == ConState:
            # Use special implementation for concrete execution
            return super().visit_AExp(node, *args, **kwargs)

        kids = [self.visit(a, *args, **kwargs) for a in node.args]
        fn = None

        if node.op == "+":
            def fn(x, y): return x + y

        elif node.op == "-":
            def fn(x, y): return x - y

        elif node.op == "*":
            def fn(x, y): return x * y

        elif node.op == "/":
            def fn(x, y): return x / y

        assert fn is not None
        return reduce(fn, kids)

    def visit_IntVar(self, node, *args, **kwargs):
        st = kwargs['state']
        if type(st) in [SymState, ConState]:
            return kwargs['state'].env[node.name]
        return kwargs['state'].symState.env[node.name]

    def visit_AsgnStmt(self, node, *args, **kwargs):
        st = kwargs['state']
        assignSymValue = self.visit(node.rhs, *args, **kwargs)
        newVar = z3.FreshInt(node.lhs.name)
        st.add_pc(newVar == assignSymValue)
        # sym
        st.symState.env[node.lhs.name] = newVar
        # con
        st.conState.env[node.lhs.name] = newVar

        conKwargs = copy.deepcopy(kwargs)
        conKwargs["state"] = st.conState
        assignConValue = self.visit(node.rhs, *args, **conKwargs)
        st.conState.add_concrete_var(node.lhs.name, assignConValue)
        return st

    def visit_IfStmt(self, node, *args, **kwargs):
        cond = self.visit(node.cond, *args, **kwargs)
        # Create two potential states here, if statement being True and statement being False
        # trueState enters then block, falseState enters else block
        trueStateKwargs = copy.deepcopy(kwargs)
        falseStateKwargs = copy.deepcopy(kwargs)

        newStates = []
        currentStateKwargs = None
        laterStateKwargs = None

        trueStateKwargs['state'].add_pc(cond)
        skip = False
        if not trueStateKwargs['state'].is_con_empty():
            # Con[cond] is feasible, trueStateKwargs will be executed later
            laterStateKwargs = trueStateKwargs
            skip = True

        falseStateKwargs['state'].add_pc(z3.Not(cond))
        if not falseStateKwargs['state'].is_con_empty():
            # Con[not cond] is feasible, falseStateKwargs will be executed later
            if not skip:
                laterStateKwargs = falseStateKwargs
        currentStateKwargs = trueStateKwargs if laterStateKwargs == falseStateKwargs else falseStateKwargs
        # Process later state
        if laterStateKwargs == trueStateKwargs:
            trueNewStates = self.visit(
                node.then_stmt, *args, **trueStateKwargs)
            trueNewStates = self._object_tolist(trueNewStates)

        else:
            falseNewStates = []
            if node.has_else():
                falseNewStates = self.visit(
                    node.else_stmt, *args, **falseStateKwargs)
                falseNewStates = self._object_tolist(falseNewStates)

        # Process current state
        currentStateKwargs['state'].update_concrete_value()
        tmp = [currentStateKwargs['state']]
        if node.has_else() and currentStateKwargs == falseStateKwargs:
            # Visit else statement if it has one
            curNewStates = self.visit(
                node.else_stmt, *args, **currentStateKwargs)
            tmp = self._object_tolist(curNewStates)
        elif currentStateKwargs == trueStateKwargs:
            # Visit then statement
            curNewStates = self.visit(
                node.then_stmt, *args, **currentStateKwargs)
            tmp = self._object_tolist(curNewStates)
        # Save later state in current state
        if tmp:
            tmp[0].add_later_explore_state(
                [laterStateKwargs['state']])  # Enough to add once only
        else:
            tmp = [laterStateKwargs['state']]
        newStates = newStates+tmp

        return newStates

    def visit_HavocStmt(self, node, *args, **kwargs):
        import random
        st = kwargs['state']
        for v in node.vars:
            val = z3.FreshInt(v.name)
            st.symState.env[v.name] = val
            st.conState.env[v.name] = val
            st.conState.add_concrete_var(v.name)
        return st

    def visit_StmtList(self, node, *args, **kwargs):
        st = kwargs['state']
        laterStateStack = []  # save later running states(concrete results)
        trackStateList = [st]  # track current running states
        resultStateList = []  # result states
        while True:
            if not trackStateList:
                if not laterStateStack:
                    break
                # When current running states are empty, pop a later state to run
                trackStateList.append(laterStateStack.pop())

            trackNewGenStates = []
            laterStates = []
            for state in trackStateList:
                freshKwargs = copy.deepcopy(kwargs)
                freshKwargs['state'] = state
                if state.curStIndex >= len(node.stmts):
                    resultStateList.append(state)
                    continue
                stmt = node.stmts[state.curStIndex]
                newStates = self.visit(stmt, *args, **freshKwargs)
                newStates = self._object_tolist(newStates)
                trackNewGenStates += newStates
                for s in newStates:
                    # Save concrete running result, run in the next iteration
                    laterStates += s.get_later_state()

                self._assign_index(newStates, state.curStIndex + 1)
                self._assign_index(laterStates, state.curStIndex + 1)
                pass

            laterStateStack.extend(laterStates)
            trackStateList = trackNewGenStates

        finalStates = []
        for state in resultStateList:
            # Check empty state
            if state.is_empty():
                print("infeasible state: "+str(state))
            elif state.is_error():
                print(
                    "this is an error state, optionally filter it out according to https://campuswire.com/c/G2011444A/feed/145: "+str(state))
            else:
                finalStates.append(state)

        return finalStates

    def _assign_index(self, tarList, index):
        for item in tarList:
            item.curStIndex = index

    def visit_WhileStmt_NoInvariant(self, node, *args, **kwargs):
        # Rewrite the while loop in EXE style
        freshKwargs = copy.deepcopy(kwargs)
        finalStates = []
        for i in range(11):  # while loop iterate 11 times because first iterate add not cond only, which is not actually a literate
            cond = self.visit(node.cond, *args, **freshKwargs)
            trueStateKwargs = copy.deepcopy(freshKwargs)
            falseStateKwargs = copy.deepcopy(freshKwargs)
            trueStateKwargs['state'].add_pc(cond)
            falseStateKwargs['state'].add_pc(z3.Not(cond))
            if trueStateKwargs['state'].is_con_empty():
                # Check if it is not concretely feasible, update concrete value and continue
                trueStateKwargs['state'].update_concrete_value()
            if not trueStateKwargs['state'].is_con_empty():
                # Check if it is concretely feasible, continue next iteration
                self.visit(node.body, *args, **trueStateKwargs)
            if not falseStateKwargs['state'].is_empty():
                # Symbolic execution is feasible, exit the loop
                falseStateKwargs['state'].update_concrete_value()
                finalStates.append(falseStateKwargs['state'])
            # assign trueStateKwargs to freshKwargs for next iteration
            freshKwargs = trueStateKwargs

        if not finalStates and not freshKwargs['state'].is_empty():
            # All false condition execution is infeasible, add last state to final states
            finalStates.append(freshKwargs['state'])

        return finalStates


class IncState(SymState):
    def __init__(self, solver=None):
        # environment mapping variables to symbolic constants
        self.env = dict()
        # activation variables
        self.activationLiterals = set()
        # precondition activation literal
        self.precondition = None
        # path condition
        self.path = list()
        self._solver = solver
        if self._solver is None:
            self._solver = z3.Solver()

        # true if this is an error state
        self._is_error = False

    def set_precondition(self, activationLiteral):
        self.precondition = activationLiteral

    def clear_precondition(self):
        self.precondition = None

    def add_pc(self, *exp):
        """Add constraints to the path condition"""
        if self.precondition != None:
            for e in exp:
                self.path.append(z3.Implies(self.precondition, e))
                self._solver.append(z3.Implies(self.precondition, e))
        else:
            self.path.extend(exp)
            self._solver.append(exp)

    def get_new_activation_literal(self):
        return z3.FreshBool()

    def add_activation_literal(self, activationLiteral):
        if activationLiteral in self.activationLiterals:
            print("Warning: activation variables {} already defined. This shouldn't happen!".format(
                str(activationLiteral)))
        self.activationLiterals.add(activationLiteral)

    def add_state_backtrack_point(self):
        self._solver.push()

    def revert_state_backtrack(self):
        self._solver.pop(num=1)

    def is_empty_withActivation(self):
        """Check whether the current symbolic state has any concrete states, use assumption"""
        res = self._solver.check(*self.activationLiterals)
        return res == z3.unsat

    def path_activation_fork(self):
        """Fork the current state into two identical states that can evolve separately
           Retain the same solver
        """
        child = IncState(solver=self._solver)
        child.env = dict(self.env)
        child.activationLiterals = set(self.activationLiterals)
        child.precondition = self.precondition
        child.add_pc(*self.path)

        return (self, child)

    def __str__(self):
        buf = io.StringIO()
        for k, v in self.env.items():
            buf.write(str(k))
            buf.write(': ')
            buf.write(str(v))
            buf.write('\n')
        buf.write('pc: ')
        buf.write(str(self.path))
        buf.write('\n')
        buf.write('activation literals: ')
        buf.write(str(self.activationLiterals))
        buf.write('\n')
        # Below is for debugging use to get all constraints in the resolver
        # Disabled to limit printing size
        """
        buf.write('complete solver constraint: ')
        buf.write(str(self._solver))
        buf.write('\n')
        """
        return buf.getvalue()


class IncExec(SymExec):
    def visit_IfStmt(self, node, *args, **kwargs):

        cond = self.visit(node.cond, *args, **kwargs)
        st = kwargs['state']

        # Test satisfiability of both branches
        originalState, testBranch = st.path_activation_fork()
        # trueState
        testBranch.add_state_backtrack_point()
        testBranch.add_pc(cond)
        trueStateSatisfy = not testBranch.is_empty_withActivation()
        testBranch.revert_state_backtrack()
        # falseState
        testBranch.add_state_backtrack_point()
        testBranch.add_pc(z3.Not(cond))
        falseStateSatisfy = not testBranch.is_empty_withActivation()
        testBranch.revert_state_backtrack()

        # Create two potential states here, if statement being True and statement being False
        # trueState enters then block, falseState enters else block
        trueState, falseState = originalState.path_activation_fork()

        newStates = []

        # Add conditions
        if trueStateSatisfy:
            trueStateActivatorSymbol = trueState.get_new_activation_literal()
            trueState.set_precondition(trueStateActivatorSymbol)
            trueState.add_pc(cond)
            trueState.add_activation_literal(trueStateActivatorSymbol)

            # Enter then state
            trueNewStates = self.visit(node.then_stmt, *args, state=trueState)
            trueNewStates = self._object_tolist(trueNewStates)
            newStates = newStates+trueNewStates

        if falseStateSatisfy:
            falseStateActivatorSymbol = falseState.get_new_activation_literal()
            falseState.set_precondition(falseStateActivatorSymbol)
            falseState.add_pc(z3.Not(cond))
            falseState.add_activation_literal(falseStateActivatorSymbol)

            # Enter else state
            if node.has_else():
                falseNewStates = self.visit(
                    node.else_stmt, *args, state=falseState)
                falseNewStates = self._object_tolist(falseNewStates)
                newStates = newStates+falseNewStates
            else:
                newStates = newStates+[falseState]

        # Clear all precondition symbols as the entire if else block exit
        for state in newStates:
            state.clear_precondition()

        return newStates

    def visit_WhileStmt_NoInvariant(self, node, *args, **kwargs):

        cond = self.visit(node.cond, *args, **kwargs)
        st = kwargs['state']

        # Test satisfiability of both branches
        originalState, testBranch = st.path_activation_fork()
        # trueState
        testBranch.add_state_backtrack_point()
        testBranch.add_pc(cond)
        trueStateSatisfy = not testBranch.is_empty_withActivation()
        testBranch.revert_state_backtrack()
        # falseState
        testBranch.add_state_backtrack_point()
        testBranch.add_pc(z3.Not(cond))
        falseStateSatisfy = not testBranch.is_empty_withActivation()
        testBranch.revert_state_backtrack()

        self.whileDepthCounter = self.whileDepthCounter+1
        newStates = []

        # Create two potential states here,  condition being True and condition being False
        # trueState enters inside block, falseState exists
        trueState, falseState = originalState.path_activation_fork()

        # Add conditions
        if trueStateSatisfy:
            trueStateActivatorSymbol = trueState.get_new_activation_literal()
            trueState.set_precondition(trueStateActivatorSymbol)
            trueState.add_pc(cond)
            trueState.add_activation_literal(trueStateActivatorSymbol)

            # Enter true condition
            if self.whileDepthCounter <= MAX_WHILE_DEPTH:
                bodyStates = self.visit(node.body, *args, state=trueState)
                bodyStates = self._object_tolist(bodyStates)
                for state in bodyStates:
                    if not state.is_empty_withActivation():
                        _, freshState = state.path_activation_fork()
                        newGenStates = self.visit(
                            node, *args, state=freshState)
                        newGenStates = self._object_tolist(newGenStates)
                        newStates = newStates+newGenStates
            else:
                self.whileDepthCounter = 0

        # Reset loop counter if no feasible path is possible
        if len(newStates) == 0:
            self.whileDepthCounter = 0

        # Enter false condition
        if falseStateSatisfy:
            falseStateActivatorSymbol = falseState.get_new_activation_literal()
            falseState.set_precondition(falseStateActivatorSymbol)
            falseState.add_pc(z3.Not(cond))
            falseState.add_activation_literal(falseStateActivatorSymbol)

            newStates = newStates+[falseState]

        for state in newStates:
            state.clear_precondition()

        return newStates

    def visit_WhileStmt_Invariant(self, node, *args, **kwargs):

        # assert invariant first
        inv = self.visit(node.inv, *args, **kwargs)
        st = kwargs['state']
        originalState, assertInvariantState = st.path_activation_fork()

        # report assertion failure at initiation
        if not originalState.is_empty_withActivation():
            assertInvariantState.add_state_backtrack_point()
            assertInvariantState.add_pc(inv)
            if assertInvariantState.is_empty_withActivation():
                print("Invariant assertion failed before the loop entered")
            assertInvariantState.revert_state_backtrack()

        # transit to arbitrary state
        underVisitor = undef_visitor.UndefVisitor()
        underVisitor.check(node.body)
        definedVariables = underVisitor.get_defs()
        _, arbitraryNewState = originalState.path_activation_fork()

        # havoc
        for v in definedVariables:
            # arbitraryNewStateKwargs['state'].env[v.name] = z3.FreshInt(v.name)
            arbitraryNewState.env[v.name] = z3.FreshInt(v.name)

        # assume inv, add inv into path condition
        inv = self.visit(node.inv, *args, state=arbitraryNewState)
        arbitraryNewState.add_pc(inv)

        # now enters the loop
        cond = self.visit(node.cond, *args, state=arbitraryNewState)

        # Create two potential states here,  condition being True and condition being False
        # trueState enters inside block, falseState exists
        trueState, falseState = arbitraryNewState.path_activation_fork()

        # Add conditions
        """
        trueStateActivatorSymbol = trueState.get_new_activation_literal()
        trueState.set_precondition(trueStateActivatorSymbol)
        trueState.add_pc(cond)
        trueState.add_activation_literal(trueStateActivatorSymbol)
        """

        falseStateActivatorSymbol = falseState.get_new_activation_literal()
        falseState.set_precondition(falseStateActivatorSymbol)
        falseState.add_pc(z3.Not(cond))
        falseState.add_activation_literal(falseStateActivatorSymbol)

        newStates = []

        # Enter true condition
        """
        bodyStates = self.visit(node.body, *args, **trueStateKwargs)
        bodyStates = self.visit(node.body, *args, state=trueState)
        bodyStates = self._object_tolist(bodyStates)
        for state in bodyStates:
            if not state.is_empty_withActivation():
                # If inv && b is true, then inv is inductive, no need to continue https://campuswire.com/c/G2011444A/feed/193
                # Invariant should hold at the end of execution
                # freshStateKwargs = copy.deepcopy(trueStateKwargs)
                # freshStateKwargs['state'] = state
                # freshInv = self.visit(node.inv, *args, **freshStateKwargs)
                # state.add_pc(freshInv)
        
                if state.is_empty():
                    print("Invariant assertion failed at the loop ends")   
        """

        # Enter false condition
        newStates = newStates+[falseState]

        for state in newStates:
            state.clear_precondition()

        return newStates

    def visit_AssertStmt(self, node, *args, **kwargs):
        # Don't forget to print an error message if an assertion might be violated

        cond = self.visit(node.cond, *args, **kwargs)

        # Create two potential states here, one being True and one being False
        trueState, falseState = kwargs['state'].path_activation_fork()

        # Add conditions
        trueStateActivatorSymbol = trueState.get_new_activation_literal()
        trueState.set_precondition(trueStateActivatorSymbol)
        trueState.add_pc(cond)
        trueState.add_activation_literal(trueStateActivatorSymbol)

        falseStateActivatorSymbol = falseState.get_new_activation_literal()
        falseState.set_precondition(falseStateActivatorSymbol)
        falseState.add_pc(z3.Not(cond))
        falseState.add_activation_literal(falseStateActivatorSymbol)

        # Print error message when the value of states can enter the false assertion state
        if not falseState.is_empty_withActivation():
            falseState.mk_error()
            print(
                "The condition for assertion here may be violated (entering assertion false): "+str(trueState))

        # Clear precondition as assert block is complete
        trueState.clear_precondition()
        falseState.clear_precondition()

        return [trueState, falseState]

    def visit_StmtList(self, node, *args, **kwargs):
        st = kwargs['state']

        trackStates = []
        trackStates.append(st)

        for stmt in node.stmts:

            # explore executing new stmt for every previous state
            trackNewGenStates = []
            for state in trackStates:
                newStates = self.visit(stmt, *args, state=state)
                newStates = self._object_tolist(newStates)
                trackNewGenStates = trackNewGenStates+newStates

            validState = []
            for state in trackNewGenStates:
                if state.is_empty_withActivation():
                    print("infeasible state: "+str(state))
                elif state.is_error():
                    print(
                        "this is an error state, optionally filter it out according to https://campuswire.com/c/G2011444A/feed/145: "+str(state))
                else:
                    validState.append(state)

            trackStates = validState

        return trackStates


def _parse_args():
    import argparse
    ap = argparse.ArgumentParser(prog='sym',
                                 description='WLang Interpreter')
    ap.add_argument('in_file', metavar='FILE',
                    help='WLang program to interpret')
    ap.add_argument('-f', '--feature', metavar='N',
                    help="Feature flag to activate execution feature. Feature 1: Use Concolic EXE execution. Feature 2: Use Z3 Incremental feature")
    args = ap.parse_args()
    return args


def main():
    args = _parse_args()
    prg = ast.parse_file(args.in_file)
    st = SymState()
    sym = SymExec()
    execType = 'SymExec'
    if args.feature == '1':
        st = EXEState()
        sym = EXEExec()
        execType = 'EXEExec'
    elif args.feature == '2':
        st = IncState()
        sym = IncExec()
        execType = 'IncExec'

    states = sym.run(prg, st)
    if states is None:
        print('[{}]: no output states'.format(execType))
    else:
        count = 0
        for out in states:
            count = count + 1
            print('[{}]: symbolic state reached'.format(execType))
            print(out)
        print('[{}]: found'.format(execType), count, 'symbolic states')
    return 0


if __name__ == '__main__':
    sys.exit(main())
