import subprocess

from yinyang.src.parsing.Ast import Script, Assert, Term, Push, Pop, SMTLIBCommand
from z3 import Solver, z3


class ASTtoAPI:
    # define-sort
    # as const, define-const, declare-fun

    decls = {
        'Bool': lambda var: z3.Bool(var),
        'Int': lambda var: z3.Int(var),
        'Real': lambda var: z3.Real(var),
        'Array': lambda var, sorts: z3.Array(var, *sorts)
    }

    sorts = {
        'Bool': lambda: z3.BoolSort(),
        'Int': lambda: z3.IntSort(),
        'Real': lambda: z3.RealSort()
    }

    ops = {
        'not': lambda args: z3.Not(*args),
        'select': lambda args: z3.Select(*args),
        'store': lambda args: z3.Store(*args),
        'distinct': lambda args: z3.Distinct(*args),
        '=': lambda args: args[0] == args[1]
    }

    vals = {
        'Bool': lambda var: z3.BoolVal(var),
        'Int': lambda var: z3.IntVal(var),
        'Real': lambda var: z3.RealVar(var)
    }

    @staticmethod
    def get_solver(script: Script) -> Solver:
        custom_sorts = {}

        for command in script.commands:
            if isinstance(command, SMTLIBCommand) and ASTtoAPI.get_type(command.cmd_str)[0] == "declare-sort":
                decl_type = ASTtoAPI.get_type(command.cmd_str)
                custom_sorts[decl_type[1]] = z3.DeclareSort(decl_type[1])

        solver = Solver()
        variables = ASTtoAPI.get_declarations(script, custom_sorts)
        for command in script.commands:
            if isinstance(command, Assert):
                solver.add(ASTtoAPI.get_term(command.term, variables))
        return solver

    @staticmethod
    def get_type(decl: str) -> list[str]:
        if decl[0] == '(':
            return decl[1:-1].split(' ')
        else:
            return [decl]

    @staticmethod
    def get_declarations(script: Script, custom_sorts: dict[str, z3.ExprRef]) -> dict[str, z3.ExprRef]:
        smt_vars = {}
        for name in script.global_vars:
            var_type = ASTtoAPI.get_type(script.global_vars[name])

            if len(var_type) < 1:
                raise ASTtoAPIException("Couldn't get the type of var " + name)

            if len(var_type) == 1:
                if var_type[0] in ASTtoAPI.decls:
                    smt_vars[name] = ASTtoAPI.decls[var_type[0]](name)
                elif var_type[0] in custom_sorts:
                    smt_vars[name] = z3.Const(name, custom_sorts[var_type[0]])
                else:
                    raise ASTtoAPIException("Unknown declaration " + var_type[0])
                continue

            var_sorts = []
            for i in range(1, len(var_type)):
                if var_type[i] in ASTtoAPI.sorts:
                    var_sorts.append(ASTtoAPI.sorts[var_type[i]]())
                elif var_type[i] in custom_sorts:
                    var_sorts.append(custom_sorts[var_type[i]])
                else:
                    raise ASTtoAPIException("Unknown sort " + var_type[i])

            if var_type[0] not in ASTtoAPI.decls:
                raise ASTtoAPIException("Unknown declaration " + var_type[0])

            smt_vars[name] = ASTtoAPI.decls[var_type[0]](name, var_sorts)
        return smt_vars

    @staticmethod
    def get_term(term: Term, variables: dict[str, z3.ExprRef]) -> z3.ExprRef:
        if term.is_var:
            if term.name not in variables:
                raise ASTtoAPIException("Unknown variable " + term.name)
            return variables[term.name]

        if term.is_const:
            if term.type not in ASTtoAPI.vals:
                raise ASTtoAPIException("Unknown type " + term.type)
            return ASTtoAPI.vals[term.type](term.name)

        subterms = []
        for subterm in term.subterms:
            subterms.append(ASTtoAPI.get_term(subterm, variables))

        if term.op not in ASTtoAPI.ops:
            raise ASTtoAPIException("Unknown operator " + term.op)

        return ASTtoAPI.ops[term.op](subterms)


class ASTtoAPIException(Exception):
    def __init(self, message):
        self.message = message
        super.__init__(self.message)
