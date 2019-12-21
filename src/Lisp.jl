module Lisp

using Tokenize

export tokenize, parse_sexp, Token

const INTEGER = Tokens.INTEGER
const FLOAT = Tokens.FLOAT
const STRING = Tokens.STRING
const OP = Tokens.OP
const LPAREN = Tokens.LPAREN
const RPAREN = Tokens.RPAREN
const WHITESPACE = Tokens.WHITESPACE

function isliteral(t)
    (Tokens.kind(t) === INTEGER
     || Tokens.kind(t) === FLOAT
     || Tokens.kind(t) === STRING)
end

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

Base.show(io::IO, t::Token) = show(io, value(t))


"""
Chunk string `s` into sections delimited by parentheses.
"""
function parse_sexp(s)
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

export eval_sexp, eval_function, eval_op

function eval_sexp(form::Vector)
    @show "form" form
    if length(form) == 0
        return form
    elseif value(form[1]) === :function
        return eval_function(form)
    elseif value(form[1]) === :(=)
        return eval_equal(form)
    elseif kind(form[1]) === OP
        return eval_op(form)
    else
        @show form
        return cat([:UNKNOWN], form, dims=1)
    end
end

function eval_sexp(form::Token)
    return value(form)
end

function eval_function(form::Vector)
    @assert value(form[1]) === :function
    @assert form[2] isa Vector
    @assert length(form) > 2
    body = [eval_sexp(f) for f in form[3:end]]
    Expr(
        value(form[1]),
        Expr(:call, value.(form[2])...),
        [Expr(:block, b) for b in body]...)
end

function eval_op(form::Vector)
    @assert kind(form[1]) === OP
    @assert length(form) > 1

    call_op(xs...) = Expr(:call, value(form[1]), xs...)
    
    if length(form) == 2
        # unary
        arg = eval_sexp(form[2])
        return Expr(:call, form[1], arg)
    else
        # TODO handle ternary operator
        # TODO handle right associative
        # binary, so fold left
        args = [eval_sexp(f) for f in form[2:end]]
        return foldl(call_op, args[3:end], init=call_op(args[1], args[2]))
    end
end

function eval_equal(form)
    @assert value(form[1]) === :(=)
    @assert length(form) > 2
    
    if form[2] isa Vector
        # special case of function definition
        body = [eval_sexp(f) for f in form[3:end]]
        return Expr(
            value(form[1]),
            Expr(:call, value.(form[2])...),
            [Expr(:block, b) for b in body]...)
    else
        @assert length(form) == 3
        assignment_value = eval_sexp(form[3])
        return Expr(value(form[1]), value(form[2]), assignment_value)
    end
end

################################################################
# loading code
export include_stringl
function include_stringl(mod, str)
    for s in parse_sexp(str)
        expr = eval_sexp(s)
        @show expr
        Base.eval(mod, expr)
    end
end

################################################################
# utilities for testing
export dump_sexp, parse_eval_sexp

dump_sexp(sexp_str) = dump(eval_sexp(parse_sexp(sexp_str)[1]))
parse_eval_sexp(sexp_str) = eval_sexp(parse_sexp(sexp_str)[1])

end # module
