module Lisp

using Tokenize
using ReplMaker: initrepl

export tokenize, read_sexp, Token

const OP = Tokens.OP

const LPAREN = Tokens.LPAREN
const RPAREN = Tokens.RPAREN

const LSQUARE = Tokens.LSQUARE  # [
const RSQUARE = Tokens.RSQUARE  # ]

const AT_SIGN = Tokens.AT_SIGN

const INTEGER = Tokens.INTEGER
const FLOAT = Tokens.FLOAT
const STRING = Tokens.STRING
const CHAR = Tokens.CHAR

const LITERAL_KINDS = Base.IdSet{Tokens.Kind}([
    INTEGER,
    FLOAT,
    STRING,
    CHAR,
])

isliteral(t) = Tokens.kind(t) ∈ LITERAL_KINDS

const WHITESPACE = Tokens.WHITESPACE
const EQ = Tokens.EQ # =
const PLUS_EQ = Tokens.PLUS_EQ # +=
const MINUS_EQ = Tokens.MINUS_EQ # -=
const STAR_EQ = Tokens.STAR_EQ # *=
const FWD_SLASH_EQ = Tokens.FWD_SLASH_EQ # /=
const FWDFWD_SLASH_EQ = Tokens.FWDFWD_SLASH_EQ # //=
const OR_EQ = Tokens.OR_EQ # |=
const CIRCUMFLEX_EQ = Tokens.CIRCUMFLEX_EQ # ^=
const DIVISION_EQ = Tokens.DIVISION_EQ # ÷=
const REM_EQ = Tokens.REM_EQ # %=
const LBITSHIFT_EQ = Tokens.LBITSHIFT_EQ # <<=
const RBITSHIFT_EQ = Tokens.RBITSHIFT_EQ # >>=
const UNSIGNED_BITSHIFT_EQ = Tokens.UNSIGNED_BITSHIFT_EQ # >>>=
const BACKSLASH_EQ = Tokens.BACKSLASH_EQ # \=
const AND_EQ = Tokens.AND_EQ # &=
const COLON_EQ = Tokens.COLON_EQ # :=
const APPROX = Tokens.APPROX # ~
const EX_OR_EQ = Tokens.EX_OR_EQ # $=
const XOR_EQ = Tokens.XOR_EQ # ⊻=
const LAZY_AND = Tokens.LAZY_AND # &&
const LAZY_OR = Tokens.LAZY_OR # ||

const OPEQUAL_EXACTKINDS = Base.IdSet{Tokens.Kind}([
    PLUS_EQ, # +=
    MINUS_EQ, # -=
    STAR_EQ, # *=
    FWD_SLASH_EQ, # /=
    FWDFWD_SLASH_EQ, # //=
    OR_EQ, # |=
    CIRCUMFLEX_EQ, # ^=
    DIVISION_EQ, # ÷=
    REM_EQ, # %=
    LBITSHIFT_EQ, # <<=
    RBITSHIFT_EQ, # >>=
    UNSIGNED_BITSHIFT_EQ, # >>>=
    BACKSLASH_EQ, # \=
    AND_EQ, # &=
    COLON_EQ, # :=
    EX_OR_EQ, # $=
    XOR_EQ, # ⊻=
])
struct Token
    value
    token
    function Token(t::Symbol)
        new(t, nothing)
    end
    function Token(t)
        t_str = untokenize(t)
        if isliteral(t)
            t_value = Meta.parse(t_str)
        else
            t_value = Symbol(t_str)
        end
        new(t_value, t)
    end
end

value(t::Token) = t.value
token(t::Token) = t.token
kind(t::Token) = Tokens.kind(t.token)
exactkind(t::Token) = Tokens.exactkind(t.token)
startpos(t::Token) = Tokens.startpos(t.token)
isopequal(t::Token) = exactkind(t) ∈ OPEQUAL_EXACTKINDS
islazy(t::Token) = exactkind(t) === LAZY_AND || exactkind(t) === LAZY_OR


Base.show(io::IO, t::Token) = show(io, value(t))

"""
Chunk string `s` into sections delimited by parentheses and brackets.
"""
function read_sexp(s)
    forms = []
    form_stack = []
    current_form = forms
    kind_stack = Tokens.Kind[]
    for t in tokenize(s)
        if Tokens.kind(t) === LPAREN
            push!(kind_stack, LPAREN)
            push!(current_form, [])
            push!(form_stack, current_form)
            current_form = current_form[end]
            continue
        elseif Tokens.kind(t) === RPAREN
            top_kind = pop!(kind_stack)
            if top_kind !== LPAREN
                (line, col) = Tokens.startpos(t)
                msg = """
                    Encountered unexpected '$(untokenize(t))' at
                    line $(line) and column $(col)"""
                throw(DomainError(s, msg))
            end
            current_form = pop!(form_stack)
        elseif Tokens.kind(t) === LSQUARE
            push!(kind_stack, LSQUARE)
            push!(current_form, Any[Token(:ref)])
            push!(form_stack, current_form)
            current_form = current_form[end]
            continue
        elseif Tokens.kind(t) === RSQUARE
            top_kind = pop!(kind_stack)
            if top_kind !== LSQUARE
                (line, col) = Tokens.startpos(t)
                msg = """
                    Encountered unexpected '$(untokenize(t))' at
                    line $(line) and column $(col)"""
                throw(DomainError(s, msg))
            end
            current_form = pop!(form_stack)
        elseif Tokens.kind(t) === WHITESPACE
            continue
        else
            push!(current_form, Token(t))
        end

    end
    # strip empty form from trailing ENDMARKER token
    forms[1:end-1]
end

################################################################
# forms to julia expr

export parse_sexp, parse_function, parse_op

function parse_sexp(form::Vector)
    @show "form" form
    if length(form) == 0
        return form
    elseif form[1] isa Vector
        return parse_call(form)
    end

    head = value(form[1])
    if head === :function
        return parse_function(form)
    elseif head === :using
        return parse_using(form)
    elseif head === :while
        return parse_while(form)
    elseif head === :for
        return parse_for(form)
    elseif head === :ref
        return parse_ref(form)
    elseif head === :return
        return parse_return(form)
    elseif head === :module || head === :baremodule
        return parse_module(form)
    elseif head === :struct || head === :mutable
        return parse_struct(form)
    elseif head === :do
        return parse_do(form)
    elseif head === :.
        return parse_dotcall(form)
    elseif head === :(=)
        return parse_equal(form)
    elseif head === :(:)
        return parse_range(form)
    elseif isopequal(form[1])
        return parse_opequal(form)
    elseif islazy(form[1])
        return parse_lazyop(form)
    elseif kind(form[1]) === OP
        return parse_op(form)
    elseif kind(form[1]) === AT_SIGN
        return parse_macrocall(form)
    else  # must be a function call
        return parse_call(form)
    end
end

function parse_sexp(form::Token)
    if value(form) === :break
        return Expr(:break)
    else
        return value(form)
    end
end

"""
Parse

    (function (f <formals>) body<...>)

into

    function f(<formals>)
        body
        <...>
    end

"""
function parse_function(form::Vector)
    @assert value(form[1]) === :function
    @assert form[2] isa Vector
    @assert length(form) > 2
    _make_function(form)
end

function _make_function(form::Vector)
    Expr(
        value(form[1]),
        Expr(:call, parse_sexp.(form[2])...),
        Expr(:block, parse_sexp.(form[3:end])...))
end

function parse_using(form::Vector)
    @assert value(form[1]) === :using
    @assert length(form) > 1

    # TODO support `using Mod: name1`
    # TODO support `using ..Mod` for submodules
    make_module(sym) = Expr(:., sym)

    modules = make_module.(value.(form[2:end]))
    Expr(value(form[1]), modules...)
end

"""
Parse

    (f <args...>)

into

    f(<args...>)

"""
function parse_call(form::Vector)
    head = parse_sexp(form[1])
    args = [parse_sexp(f) for f in form[2:end]]
    Expr(:call, head, args...)
end

"""
Parse

    (@f <args...>)

into

    @f(<args...>)

"""
function parse_macrocall(form::Vector)
    @assert kind(form[1]) === AT_SIGN
    @assert length(form) > 1
    head = Symbol(string(value.(form[1:2])...))
    args = parse_sexp.(form[3:end])
    # LineNumberNode is required for correct parsing
    e = Expr(:macrocall, head, LineNumberNode(1, :none), args...)
    @show head args e
    e
end

"""
Parse

    [f <indices...>]

into

    f[<indices...>]

and

    [. x y <attributes...>]

into

    x.y<.<attributes...>>

and

    [:: x y <types...>]

into

    x::y<::<types...>>

"""
function parse_ref(form::Vector)
    head = parse_sexp(form[2])
    if head === :.
        function make_getfield(x, y)
            return Expr(:., x, QuoteNode(y))
        end
        return foldl(make_getfield, parse_sexp.(form[3:end]))
    elseif head === :(::)
        function make_annotation(x, y)
            return Expr(:(::), x, y)
        end
        return foldl(make_annotation, parse_sexp.(form[3:end]))
    else  # array indexing
        indices = [parse_sexp(f) for f in form[3:end]]
        return Expr(:ref, head, indices...)
    end
end

"""
Parse

    (. f <args...>)

into

    f.(<args...>)

"""
function parse_dotcall(form::Vector)
    @assert length(form) > 1
    args = [parse_sexp(f) for f in form[3:end]]
    Expr(value(form[1]), value(form[2]), Expr(:tuple, args...))
end

function parse_op(form::Vector)
    @assert kind(form[1]) === OP
    @assert length(form) > 1

    call_op(xs...) = Expr(:call, value(form[1]), xs...)

    if length(form) == 2
        # unary
        arg = parse_sexp(form[2])
        return call_op(parse_sexp(form[2]))
    else
        # TODO handle ternary operator
        # TODO handle right associative
        # binary, so fold
        args = [parse_sexp(f) for f in form[2:end]]
        return foldr(call_op, args)
    end
end

function parse_equal(form)
    @assert value(form[1]) === :(=)
    @assert length(form) > 2
    @show "equal" form

    if (form[2] isa Vector) && (value(form[2][1]) !== :ref)
        # special case of function definition
        _make_function(form)
    else
        @assert length(form) == 3
        destination = parse_sexp(form[2])
        assignment_value = parse_sexp(form[3])
        return Expr(value(form[1]), destination, assignment_value)
    end
end

parse_range(form::Vector) = parse_call(form)

function parse_opequal(form::Vector)
    @assert isopequal(form[1])
    @assert length(form) == 3
    op = value(form[1])
    lhs = value(form[2])
    rhs = parse_sexp(form[3])
    Expr(op, lhs, rhs)
end

function parse_lazyop(form::Vector)
    @assert islazy(form[1])
    @assert length(form) > 2
    op = value(form[1])
    call_op(lhs, rhs) = Expr(op, lhs, rhs)
    args = [parse_sexp(f) for f in form[2:end]]
    return foldr(call_op, args)
end

function parse_while(form::Vector)
    @assert value(form[1]) === :while
    @assert length(form) > 2
    condition = parse_sexp(form[2])
    body = [parse_sexp(f) for f in form[3:end]]
    Expr(:while, condition, Expr(:block, body...))
end

"""
Convert

    (for (i itr) body)

into

    for i = itr
        body
    end

and

    (for ((i itr1) (j itr2)) body)

into

    for i = itr1, j = itr2
        body
    end

"""
function parse_for(form::Vector)
    @assert value(form[1]) === :for
    @assert length(form) > 2

    make_itr(form) = Expr(:(=), value(form[1]), parse_sexp(form[2]))

    head = value(form[1])
    body = parse_sexp.(form[3:end])
    if form[2][1] isa Vector
        # multiple iterators
        itrs = make_itr.(form[2])
        return Expr(head, Expr(:block, itrs...), Expr(:block, body...))
    else
        # single iterator
        itr = make_itr(form[2])
        return Expr(head, itr, Expr(:block, body...))
    end
end

function parse_return(form::Vector)
    @assert value(form[1]) === :return
    if length(form) == 2
        ret = parse_sexp(form[2])
        Expr(value(form[1]), ret)
    else  # length(form) > 2
        ret = Expr(:tuple, parse_sexp.(form[2:end])...)
        Expr(value(form[1]), ret)
    end
end

function parse_module(form::Vector)
    @assert value(form[1]) === :module || value(form[1]) === :baremodule
    @assert length(form) > 1
    function make_module(form, import_base)
        body = parse_sexp.(form[3:end])
        Expr(:module, import_base, value(form[2]), Expr(:block, body...))
    end

    if value(form[1]) === :module
        make_module(form, true)
    else  # baremodule
        make_module(form, false)
    end
end

function parse_struct(form::Vector)
    head = value(form[1])
    @assert (
        head === :struct || (head === :mutable && value(form[2]) === :struct))
    @assert length(form) > 1

    function make_struct(form, is_mutable, name, body)
        Expr(:struct, is_mutable, name, Expr(:block, body...))
    end

    is_mutable = head === :mutable
    name_index = is_mutable ? 3 : 2
    name = value(form[name_index])
    body = parse_sexp.(form[(name_index + 1):end])
    return make_struct(form, is_mutable, name, body)
end

"""
Parse

    (do (f <args...>) (<formals...>) <body...>)

into

    do f(<args...>) <formals...>
        <body...>
    end

"""
function parse_do(form::Vector)
    head = value(form[1])
    @assert head === :do
    @assert length(form) > 3

    func = parse_sexp(form[2])
    formals = Expr(:tuple, value.(form[3])...)
    body = parse_sexp.(form[4:end])
    Expr(head, func, Expr(:->, formals, Expr(:block, body...)))
end

################################################################
# loading code
export include_stringl, includel
function include_stringl(mod, str)
    for s in read_sexp(str)
        expr = parse_sexp(s)
        @show expr
        Base.eval(mod, expr)
    end
end

function includel(mod, filename)
    open(filename, "r") do source_file
        source = read(source_file, String)
        include_stringl(mod, source)
    end
end

################################################################
# utilities for testing
export dump_sexp, parse_sexp_string, enable_repl

dump_sexp(sexp_str) = dump(parse_sexp(read_sexp(sexp_str)[1]))
parse_sexp_string(sexp_str) = parse_sexp(read_sexp(sexp_str)[1])
function enable_repl()
    initrepl(parse_sexp_string;
        prompt_text="jlisp> ",
        prompt_color=:blue,
        start_key=')',
        mode_name="JLisp_mode",
    )
end

end # module
