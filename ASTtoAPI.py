from yinyang.src.parsing.Ast import Script, Assert, Term, Push, Pop, SMTLIBCommand, DeclareFun, DefineFun, DeclareConst
from z3 import Solver, z3, DeclareSort


def operator_fun(fun, args, init):
    if len(args) == 0:
        return init
    return operator_fun(fun, args[1:], fun(init, args[0]))


class ASTtoAPI:
    # as const, declare-fun
    decls = {
        'Bool': lambda var: z3.Bool(var),
        'Int': lambda var: z3.Int(var),
        'Real': lambda var: z3.Real(var),
        'Array': lambda var, args: z3.Array(var, *args),
        'BitVec': lambda var, args: z3.BitVec(var, args[0]),
        'FloatingPoint': lambda var, args: z3.FP(var, args[0])
    }

    sorts = {
        'Bool': lambda: z3.BoolSort(),
        'Int': lambda: z3.IntSort(),
        'Real': lambda: z3.RealSort(),
        'BitVec': lambda val: z3.BitVecSort(int(val[0])),
        'FloatingPoint': lambda val: z3.FPSort(int(val[0]), int(val[1]))
    }

    ops = {
        'not': lambda args: z3.Not(*args),
        'select': lambda args: z3.Select(*args),
        'store': lambda args: z3.Store(*args),
        'distinct': lambda args: z3.Distinct(*args),
        'ite': lambda args: z3.If(*args),
        'abs': lambda args: z3.Abs(args[0]),
        'and': lambda args: z3.And(*args),
        'or': lambda args: z3.Or(*args),
        'xor': lambda args: z3.Xor(*args),
        '=': lambda args: args[0] == args[1],
        '+': lambda args: args[0] + args[1],
        '-': lambda args: -args[0] if len(args) == 1 else args[0] - args[1],
        '*': lambda args: args[0] * args[1],
        '>': lambda args: args[0] > args[1],
        '>=': lambda args: args[0] >= args[1],
        '<': lambda args: args[0] < args[1],
        '<=': lambda args: args[0] <= args[1],
        'bvadd': lambda args: operator_fun(lambda a, b: a + b, args, 0),
        'bvsub': lambda args: args[0] - args[1],
        'bvneg': lambda args: -args[0],
        'bvmul': lambda args: args[0] * args[1],
        'bvurem': lambda args: z3.URem(args[0], args[1]),
        'bvsrem': lambda args: z3.SRem(args[0], args[1]),
        'bvsmod': lambda args: args[0] % args[1],
        'bvudiv': lambda args: z3.UDiv(args[0], args[1]),
        'bvsdiv': lambda args: args[0] / args[1],
        'bvor': lambda args: args[0] | args[1],
        'bvand': lambda args: args[0] & args[1],
        'bvxor': lambda args: args[0] ^ args[1],
        'bvnot': lambda args: ~args[0],
        'bvnand': lambda args: ~(args[0] & args[1]),
        'bvnor': lambda args: ~(args[0] | args[1]),
        'bvxnor': lambda args: ~(args[0] ^ args[1]),
        'bvshl': lambda args: args[0] << args[1],
        'bvlshr': lambda args: z3.LShR(args[0], args[1]),
        'bvashr': lambda args: args[0] >> args[1],
        'bvsle': lambda args: args[0] <= args[1],
        'bvslt': lambda args: args[0] < args[1],
        'bvsgt': lambda args: args[0] > args[1],
        'bvsge': lambda args: args[0] >= args[1],
        'bvule': lambda args: z3.ULE(*args),
        'bvult': lambda args: z3.ULT(*args),
        'bvugt': lambda args: z3.UGT(*args),
        'bvuge': lambda args: z3.UGE(*args),
        'bveq': lambda args: args[0] == args[1],
        'simplify': lambda args: z3.simplify(*args),
        'concat': lambda args: z3.Concat(*args),
        'extract': lambda args: z3.Extract(int(args[0]), int(args[1]), args[2]),
        'zero_extend': lambda args: z3.ZeroExt(int(args[0]), args[1]),
        'sign_extend': lambda args: z3.SignExt(int(args[0]), args[1]),
        'rotate-left': lambda args: z3.RotateLeft(int(args[1]), args[0]),
        'rotate-right': lambda args: z3.RotateRight(int(args[1]), args[0]),
        'repeat': lambda args: z3.RepeatBitVec(int(args[0]), args[1]),
        '=>': lambda args: z3.Implies(*args),
        'fp.add': lambda args: z3.fpAdd(*args),
        'fp.mul': lambda args: z3.fpMul(*args),
        'fp.sub': lambda args: z3.fpSub(*args),
        'fp.div': lambda args: z3.fpDiv(*args),
        'fp.max': lambda args: z3.fpMax(*args),
        'fp.min': lambda args: z3.fpMin(*args),
        'fp.sqrt': lambda args: z3.fpSqrt(*args),
        'fp.abs': lambda args: z3.fpAbs(*args),
        'fp.eq': lambda args: z3.fpEQ(*args),
        'fp.rem': lambda args: z3.fpRem(*args),
        'fp.isNan': lambda args: z3.fpIsNaN(*args),
        'fp.isInfinite': lambda args: z3.fpIsInf(*args),
        'fp.isZero': lambda args: z3.fpIsZero(*args),
        'fp': lambda args: z3.fpFP(*args),
        'fp.isPositive': lambda args: z3.fpIsPositive(*args),
        'fp.isNaN': lambda args: z3.fpIsNaN(*args),
        'fp.isNormal': lambda args: z3.fpIsNormal(*args),
        'fp.isSubnormal': lambda args: z3.fpIsSubnormal(*args),
        'fp.isNegative': lambda args: z3.fpIsNegative(*args),
        'fp.lt': lambda args: z3.fpLT(*args),
        'fp.leq': lambda args: z3.fpLEQ(*args),
        'fp.gt': lambda args: z3.fpGT(*args),
        'fp.geq': lambda args: z3.fpGEQ(*args),
        'fp.roundToIntegral': lambda args: z3.fpRoundToIntegral(*args),
        'fp.neg': lambda args: z3.fpNeg(*args)
    }

    vals = {
        'Bool': lambda var: z3.BoolVal(False) if 'false' in var[0].lower() or '0' in var[0] else z3.BoolVal(True),
        'Int': lambda var: z3.IntVal(var[0]),
        'Real': lambda var: z3.RealVar(var[0]),
        'BitVec': lambda var: z3.BitVecVal(int(var[0]), int(var[1]))
    }

    RM = {
        "RTP": lambda: z3.RTP(),
        "RTN": lambda: z3.RTN(),
        "RTZ": lambda: z3.RTZ(),
        "RNA": lambda: z3.RNA(),
        "RNE": lambda: z3.RNE(),
        "roundNearestTiesToEven": lambda: z3.RoundNearestTiesToEven(),
        "roundNearestTiesToAway": lambda: z3.RoundNearestTiesToAway(),
        "roundTowardZero": lambda: z3.RoundTowardZero(),
        "roundTowardNegative": lambda: z3.RoundTowardNegative(),
        "roundTowardPositive": lambda: z3.RoundTowardPositive()
    }

    @staticmethod
    def get_solver(script: Script) -> Solver:
        custom_sorts = {}
        variables = {}
        solver = Solver()
        for command in script.commands:
            #  add custom sort
            if isinstance(command, SMTLIBCommand) and ASTtoAPI.parse_type_string(command.cmd_str)[0] == "declare-sort":
                decl_type = ASTtoAPI.parse_type_string(command.cmd_str)
                custom_sorts[decl_type[1]] = z3.DeclareSort(decl_type[1])

            elif isinstance(command, SMTLIBCommand) and ASTtoAPI.parse_type_string(command.cmd_str)[0] == "define-sort":
                decl_type = ASTtoAPI.parse_type_string(command.cmd_str)
                name = decl_type[1]
                if decl_type[3] == '()':
                    raise ASTtoAPIException("The input of define sort is not empty")
                decl_type = ASTtoAPI.parse_type_string(" ".join(decl_type[3:]))
                custom_sorts[name] = ASTtoAPI.sorts[decl_type[0]](decl_type[1:])

            # declare-const
            elif isinstance(command, DeclareConst):
                variables[command.symbol] = ASTtoAPI.get_declaration(command.symbol, command.sort, custom_sorts)

            # declare const functions
            elif isinstance(command, DeclareFun) and len(command.input_sort) == 0:
                variables[command.symbol] = ASTtoAPI.get_declaration(command.symbol, command.output_sort, custom_sorts)

            # declare non-const functions
            elif isinstance(command, DeclareFun) and len(command.input_sort) > 0:
                input_sorts = ASTtoAPI.parse_sort_string(command.input_sort)
                input_sorts = [ASTtoAPI.parse_type_string(elem) for elem in input_sorts]

                output_sorts = ASTtoAPI.parse_sort_string(command.output_sort)
                output_sorts = [ASTtoAPI.parse_type_string(elem) for elem in output_sorts]

                sorts = []
                for sort in input_sorts + output_sorts:
                    if sort[0] in ASTtoAPI.sorts:
                        if len(sort) == 1:
                            sorts.append(ASTtoAPI.sorts[sort[0]]())
                        else:
                            sorts.append(ASTtoAPI.sorts[sort[0]](sort[1:]))
                    elif sort[0] in custom_sorts:
                        sorts.append(custom_sorts[sort[0]])
                    else:
                        raise ASTtoAPIException("Unknown sort " + str(sort))

                variables[command.symbol] = z3.Function(command.symbol, sorts)

            # define-fun
            elif isinstance(command, DefineFun):
                if command.sorted_vars == '':
                    variables[command.symbol] = ASTtoAPI.get_term(command.term, variables, {}, custom_sorts)
                    continue

                sorted_vars_str = ASTtoAPI.parse_sort_string(command.sorted_vars)
                sorted_vars = {}
                sorts = []
                for var in sorted_vars_str:
                    var = ASTtoAPI.parse_type_string(var)
                    sorted_vars[var[0]] = ASTtoAPI.get_declaration(var[0], "(" + " ".join(var[1:]) + ")", custom_sorts)
                    if var[1] in ASTtoAPI.sorts:
                        if len(var) > 2:
                            sorts.append(ASTtoAPI.sorts[var[1]](var[2:]))
                        else:
                            sorts.append(ASTtoAPI.sorts[var[1]]())
                    elif var[1] in custom_sorts:
                        sorts.append(custom_sorts[var[1]])
                    else:
                        raise ASTtoAPIException("Unknown sort " + var[1] + " in " + command.sorted_vars)

                output_sort = ASTtoAPI.parse_sort_string(command.sort)
                if output_sort[0] in ASTtoAPI.sorts:
                    if len(output_sort) > 2:
                        sorts.append(ASTtoAPI.sorts[output_sort[0]](output_sort[1:]))
                    else:
                        sorts.append(ASTtoAPI.sorts[output_sort[0]]())
                elif output_sort[0] in custom_sorts:
                    sorts.append(custom_sorts[output_sort[0]])
                else:
                    raise ASTtoAPIException("Unknown sort " + output_sort[0] + " in " + command.sort)

                # >> > f = Function('f', IntSort(), IntSort(), IntSort())
                # >> >  # Z3 replaces x and y with bound variables when ForAll is executed.
                # >> > q = ForAll([x, y], f(x, y) == x + y)
                # >> > q.body()
                # f(Var(1), Var(0)) == Var(1) + Var(0)

                func_decl = z3.Function(command.symbol, *sorts)
                func_body = ASTtoAPI.get_term(command.term, variables, sorted_vars, custom_sorts)
                func_forall = z3.ForAll(list(sorted_vars.values()), func_decl(*list(sorted_vars.values())) == func_body)
                solver.add(func_forall)
                variables[command.symbol] = func_decl

        ASTtoAPI.get_declarations(script, custom_sorts, variables)
        for command in script.commands:
            if isinstance(command, Assert):
                solver.add(ASTtoAPI.get_term(command.term, variables, {}, custom_sorts))
        return solver

    @staticmethod
    def parse_sort_string(sort: str) -> list:
        sort += ' '
        bal = 0
        ind = -1
        res = []
        for i in range(len(sort)):
            if sort[i] == '(' and bal > 0:
                bal += 1
            elif sort[i] == '(' and bal == 0:
                bal += 1
                ind = i
            elif sort[i] == ')' and bal == 1:
                subsort = sort[ind:i + 1]
                if '(' in subsort[ind + 1:i] or ')' in subsort[ind + 1:i]:
                    raise Exception("Unknown sort " + sort)
                res.append(subsort)
                bal -= 1
            elif sort[i] == ')' and bal > 1:
                bal -= 1
            elif bal == 0 and (
                    (i == 0 and sort[i] != ' ') or (i != 0 and sort[i - 1] == ' ' and sort[i] not in ['(', ')', ' '])):
                ind = i
            elif bal == 0 and (
                    (i == 0 and sort[i] == ' ') or (i != 0 and sort[i - 1] not in ['(', ')', ' '] and sort[i] == ' ')):
                subsort = sort[ind:i]
                res.append(subsort)
            else:
                continue
        return res

    @staticmethod
    def parse_type_string(decl: str) -> list[str]:
        str_decl = str(decl)
        if str_decl[0] == '(':
            res = str_decl[1:-1].split(' ')
            if res[0] == '_':
                res = res[1:]
            if 'bv' in res[0]:  # BitVector constant
                res = ['BitVec'] + [res[0][2:]] + res[1:]
            return res
        else:
            return [str_decl]

    @staticmethod
    def get_declarations(script: Script, custom_sorts: dict[str, z3.ExprRef], variables: dict[str, z3.ExprRef]) -> []:
        for name in script.global_vars:
            if name in variables:  # skip declare-fun statement
                continue

            var_type = ASTtoAPI.parse_type_string(script.global_vars[name])

            if len(var_type) < 1:
                raise ASTtoAPIException("Couldn't get the type of var " + name)

            if len(var_type) == 1:
                if var_type[0] in ASTtoAPI.decls:
                    variables[name] = ASTtoAPI.decls[var_type[0]](name)
                elif var_type[0] in custom_sorts:
                    variables[name] = z3.Const(name, custom_sorts[var_type[0]])
                else:
                    raise ASTtoAPIException("Unknown declaration " + var_type[0])
                continue

            var_sorts = []
            for i in range(1, len(var_type)):
                if var_type[0] == 'Array' and var_type[i] in ASTtoAPI.sorts:
                    var_sorts.append(ASTtoAPI.sorts[var_type[i]]())
                elif var_type[0] == 'Array' and var_type[i] in custom_sorts:
                    var_sorts.append(custom_sorts[var_type[i]])
                elif var_type[0] == 'BitVec':
                    var_sorts.append(z3.BitVecSort(int(var_type[i])))
                elif var_type[0] == 'FloatingPoint':
                    var_sorts.append(z3.FPSort(int(var_type[1]), int(var_type[2])))
                    break
                else:
                    raise ASTtoAPIException("Unknown sort " + var_type[i])

            if var_type[0] not in ASTtoAPI.decls:
                raise ASTtoAPIException("Unknown declaration " + var_type[0])

            variables[name] = ASTtoAPI.decls[var_type[0]](name, var_sorts)

    @staticmethod
    def get_declaration(name: str, v_type: str, custom_sorts: dict[str, z3.ExprRef]) -> z3.ExprRef:
        var_type = ASTtoAPI.parse_type_string(v_type)

        if len(var_type) < 1:
            raise ASTtoAPIException("Couldn't get the type of var " + name)

        if len(var_type) == 1:
            if var_type[0] in ASTtoAPI.decls:
                return ASTtoAPI.decls[var_type[0]](name)
            elif var_type[0] in custom_sorts:
                return z3.Const(name, custom_sorts[var_type[0]])
            else:
                raise ASTtoAPIException("Unknown declaration " + var_type[0])

        var_sorts = []
        for i in range(1, len(var_type)):
            if var_type[0] == 'Array' and var_type[i] in ASTtoAPI.sorts:
                var_sorts.append(ASTtoAPI.sorts[var_type[i]]())
            elif var_type[0] == 'Array' and var_type[i] in custom_sorts:
                var_sorts.append(custom_sorts[var_type[i]])
            elif var_type[0] == 'BitVec':
                var_sorts.append(z3.BitVecSort(int(var_type[i])))
            elif var_type[0] == 'FloatingPoint':
                var_sorts.append(z3.FPSort(int(var_type[1]), int(var_type[2])))
                break
            else:
                raise ASTtoAPIException("Unknown sort " + var_type[i])

        if var_type[0] not in ASTtoAPI.decls:
            raise ASTtoAPIException("Unknown declaration " + var_type[0])

        return ASTtoAPI.decls[var_type[0]](name, var_sorts)

    @staticmethod
    def get_term(term: Term, variables: dict[str, z3.ExprRef], let_variables: dict[str, z3.ExprRef],
                 custom_sorts: dict[str, z3.ExprRef]) -> z3.ExprRef:
        if str(term) in ASTtoAPI.RM:  # term is rounding mode
            return ASTtoAPI.RM[str(term)]()

        if term.name is not None and term.name[0] == '#':  # const value in given numeral system
            if term.name[1] == 'b':  # binary value
                return z3.BitVecVal(int(term.name[2:], 2), len(term.name) - 2)

            if term.name[1] == 'x':  # hexadecimal value
                return z3.BitVecVal(int(term.name[2:], 16), (len(term.name) - 2) * 4)

        if term.is_var:
            if term.name in variables:
                return variables[term.name]
            elif term.name in let_variables:
                return let_variables[term.name]
            else:
                raise ASTtoAPIException("Unknown variable " + term.name)

        if term.is_const:
            term_type = term.type
            if 'bv' in term.name:  # BitVector constant
                term_type = ASTtoAPI.parse_type_string(term.name)
                return ASTtoAPI.vals[term_type[0]](term_type[1:])
            if term_type not in ASTtoAPI.vals:
                raise ASTtoAPIException("Unknown type " + term_type)
            return ASTtoAPI.vals[term_type](term.name)

        if len(term.subterms) == 0:
            raise ASTtoAPIException("Unknown term" + str(term))

        if term.let_terms is not None:  # the term contains let statement
            new_let_variables = {}
            for i in range(len(term.let_terms)):
                new_let_variables[term.var_binders[i]] = ASTtoAPI.get_term(term.let_terms[i], variables, let_variables,
                                                                           custom_sorts)

            for let_var in let_variables:
                new_let_variables[let_var] = let_variables[let_var]  # add exception

            return ASTtoAPI.get_term(term.subterms[0], variables, new_let_variables, custom_sorts)

        if term.quantifier == 'forall' or term.quantifier == 'exists':  # the term if forall or exists statement
            quantifier_vars = {}
            for i in range(len(term.quantified_vars[0])):
                quantifier_vars[term.quantified_vars[0][i]] = \
                    ASTtoAPI.get_declaration(term.quantified_vars[0][i], term.quantified_vars[1][i], custom_sorts)

            new_let_vars = {}
            for let_var in let_variables:
                new_let_vars[let_var] = let_variables[let_var]
            for q_var in quantifier_vars:
                new_let_vars[q_var] = quantifier_vars[q_var]

            if term.quantifier == 'forall':
                return z3.ForAll(list(quantifier_vars.values()),
                                 ASTtoAPI.get_term(term.subterms[0], variables, new_let_vars, custom_sorts))

            if term.quantifier == 'exists':
                return z3.Exists(list(quantifier_vars.values()),
                                 ASTtoAPI.get_term(term.subterms[0], variables, new_let_vars, custom_sorts))

        term_op = ASTtoAPI.parse_type_string(term.op)
        if str(term_op[0]) not in ASTtoAPI.ops and str(term_op[0]) not in variables:
            print(term)
            raise ASTtoAPIException("Unknown operator " + str(term.op))

        subterms = []
        for subterm in term.subterms:
            subterms.append(ASTtoAPI.get_term(subterm, variables, let_variables, custom_sorts))

        if str(term_op[0]) in variables:  # operator is declared function
            return variables[str(term_op[0])](subterms)

        return ASTtoAPI.ops[term_op[0]](term_op[1:] + subterms)


class ASTtoAPIException(Exception):
    def __init(self, message):
        self.message = message
        super.__init__(self.message)
