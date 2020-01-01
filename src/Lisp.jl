module Lisp

using Tokenize

export tokenize, read_sexp, Token

const INTEGER = Tokens.INTEGER
const FLOAT = Tokens.FLOAT
const STRING = Tokens.STRING
const OP = Tokens.OP
const LPAREN = Tokens.LPAREN
const RPAREN = Tokens.RPAREN
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

const LITERAL_KINDS = Base.IdSet{Tokens.Kind}([
    INTEGER,
    FLOAT,
    STRING,
])

isliteral(t) = Tokens.kind(t) ∈ LITERAL_KINDS

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

isopequal(t::Token) = exactkind(t) ∈ OPEQUAL_EXACTKINDS
islazy(t::Token) = exactkind(t) === LAZY_AND || exactkind(t) === LAZY_OR

struct Token
    value
    token
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

Base.show(io::IO, t::Token) = show(io, value(t))


"""
Chunk string `s` into sections delimited by parentheses.
"""
function read_sexp(s)
    forms = []
    form_stack = []
    current_form = forms
    for t in tokenize(s)
        if Tokens.kind(t) === LPAREN
            push!(current_form, [])
            push!(form_stack, current_form)
            current_form = current_form[end]
            continue
        elseif Tokens.kind(t) === RPAREN
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
    head = value(form[1])
    if length(form) == 0
        return form
    elseif head === :function
        return parse_function(form)
    elseif head === :using
        return parse_using(form)
    elseif head === :while
        return parse_while(form)
    elseif head === :for
        return parse_for(form)
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
    body = [parse_sexp(f) for f in form[3:end]]
    Expr(
        value(form[1]),
        Expr(:call, value.(form[2])...),
        Expr(:block, body...))
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
    args = [parse_sexp(f) for f in form[2:end]]
    Expr(:call, value(form[1]), args...)
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
        return Expr(:call, form[1], arg)
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

    if form[2] isa Vector
        # special case of function definition
        _make_function(form)
    else
        @assert length(form) == 3
        assignment_value = parse_sexp(form[3])
        return Expr(value(form[1]), value(form[2]), assignment_value)
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
export dump_sexp, parse_sexp_string

dump_sexp(sexp_str) = dump(parse_sexp(read_sexp(sexp_str)[1]))
parse_sexp_string(sexp_str) = parse_sexp(read_sexp(sexp_str)[1])

end # module
