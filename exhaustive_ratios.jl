#!/usr/bin/env julia
using Printf

# ----------------------------
# Bit helpers
# ----------------------------
function bit(j::Int)::UInt64
    UInt64(1) << (j-1)
end

function popcount64(x::UInt64)::Int
    count_ones(x)
end

function pairs_list(n::Int)
    pairs = Vector{Tuple{Int,Int}}()
    for i in 1:n-1, j in i+1:n
        push!(pairs, (i,j))
    end
    return pairs
end

# base-3 increment on digits (UInt8 in {0,1,2}); least-significant first
function increment_base3!(digits::Vector{UInt8})::Bool
    i = 1
    while i <= length(digits)
        if digits[i] < 0x02
            digits[i] += 0x01
            return true
        else
            digits[i] = 0x00
            i += 1
        end
    end
    return false
end

# Build outmask from digits:
# digits[k] corresponds to pairs[k] = (i<j):
#   0: none
#   1: i->j
#   2: j->i
function build_outmask!(outmask::Vector{UInt64}, digits::Vector{UInt8}, pairs)
    fill!(outmask, UInt64(0))
    for k in 1:length(pairs)
        (i,j) = pairs[k]
        c = digits[k]
        if c == 0x01
            outmask[i] |= bit(j)
        elseif c == 0x02
            outmask[j] |= bit(i)
        end
    end
end

# Outdegree stats + number of directed edges
function degree_stats(outmask::Vector{UInt64}, n::Int)
    d = Vector{Int}(undef, n)
    m_edges = 0
    for v in 1:n
        dv = popcount64(outmask[v])
        d[v] = dv
        m_edges += dv
    end
    return minimum(d), maximum(d), m_edges
end

# Compute (d2(v), d1(v)) based quantities for one vertex
function d2_exact(outmask::Vector{UInt64}, v::Int)
    N1 = outmask[v]
    d1 = popcount64(N1)
    if d1 == 0
        return 0, 0
    end
    N2raw = UInt64(0)
    tmp = N1
    while tmp != 0
        lowbit = tmp & (~tmp + 1)
        u = trailing_zeros(lowbit) + 1
        N2raw |= outmask[u]
        tmp &= tmp - 1
    end
    N2 = (N2raw & ~N1) & ~bit(v)
    d2 = popcount64(N2)
    return d2, d1
end

# SENSIBLE per-graph diagnostics:
#   Δ(D) = max_v (d2 - d1)
#   R(D) = max_v (d2/d1) over vertices with d1>0  (in restricted class all d1>0)
function graph_metrics(outmask::Vector{UInt64}, n::Int)
    Δ = -typemax(Int)
    R = 0.0
    argΔ = 1
    for v in 1:n
        d2, d1 = d2_exact(outmask, v)
        if d1 == 0
            # in restricted classes we won't allow this; still safe
            if 0 > Δ
                Δ = 0
                argΔ = v
            end
            continue
        end
        margin = d2 - d1
        if margin > Δ
            Δ = margin
            argΔ = v
        end
        ratio = d2 / d1
        if ratio > R
            R = ratio
        end
    end
    return Δ, R, argΔ
end

function digits_to_edgelist(digits::Vector{UInt8}, pairs)
    buf = IOBuffer()
    for k in 1:length(pairs)
        (i,j) = pairs[k]
        c = digits[k]
        if c == 0x01
            @printf(buf, "%d -> %d\n", i, j)
        elseif c == 0x02
            @printf(buf, "%d -> %d\n", j, i)
        end
    end
    return String(take!(buf))
end

# Keep Top-K most dangerous graphs in restricted class by:
#   (Δ(D), R(D), density) ascending
# item stored: (Δ, R, density, min_outdeg, max_outdeg, digits_copy)
function topk_insert!(top::Vector, item, K::Int)
    push!(top, item)
    sort!(top, by = x -> (x[1], x[2], x[3]))
    if length(top) > K
        pop!(top)
    end
end

# ----------------------------
# CLI parsing
# ----------------------------
function parse_args()
    n = nothing
    topk = 20
    progress = 1_000_000
    minout = 1              # <-- key new parameter: ignore trivial graphs

    i = 1
    while i <= length(ARGS)
        arg = ARGS[i]
        if arg == "--topk"
            topk = parse(Int, ARGS[i+1]); i += 2
        elseif arg == "--progress"
            progress = parse(Int, ARGS[i+1]); i += 2
        elseif arg == "--minout"
            minout = parse(Int, ARGS[i+1]); i += 2
        else
            if n === nothing
                n = parse(Int, arg); i += 1
            else
                error("Unrecognized argument: $arg")
            end
        end
    end

    n === nothing && error("Provide n, e.g. julia exhaustive_ratios.jl 6")
    return (n=n, topk=topk, progress=progress, minout=minout)
end

# ----------------------------
# Main
# ----------------------------
function main()
    args = parse_args()
    n = args.n
    K = args.topk
    progress = args.progress
    minout_req = args.minout

    if n > 63
        error("UInt64 bitmask representation requires n <= 63.")
    end
    pairs = pairs_list(n)
    m = length(pairs)

    @printf("n=%d, pairs=%d, total graphs=3^%d = %s\n", n, m, m, string(big(3)^big(m)))
    @printf("Restricted class: min outdegree >= %d\n", minout_req)
    if n > 6
        @printf("WARNING: exhaustive beyond n=6 is typically not laptop-feasible.\n")
    end

    digits = fill(UInt8(0), m)
    outmask = fill(UInt64(0), n)

    checked_total = 0
    checked_restricted = 0
    violations_restricted = 0

    # Extremal stats over restricted family
    min_Δ = typemax(Int)
    min_R = Inf

    topK = Any[]

    while true
        checked_total += 1
        build_outmask!(outmask, digits, pairs)

        min_out, max_out, m_edges = degree_stats(outmask, n)
        if min_out >= minout_req
            checked_restricted += 1

            density = m_edges / (n*(n-1))
            Δ, R, _ = graph_metrics(outmask, n)

            # If conjecture is violated within restricted class
            if Δ < 0
                violations_restricted += 1
            end

            if Δ < min_Δ
                min_Δ = Δ
            end
            if R < min_R
                min_R = R
            end

            topk_insert!(topK, (Δ, R, density, min_out, max_out, copy(digits)), K)

            if progress > 0 && (checked_restricted % progress == 0)
                @printf("restricted_checked=%d | restricted_violations=%d | minΔ=%d | minR=%.6f\n",
                        checked_restricted, violations_restricted, min_Δ, min_R)
            end
        end

        if !increment_base3!(digits)
            break
        end
    end

    println("\n==== FINAL SUMMARY ====")
    @printf("n=%d\n", n)
    @printf("total graphs checked: %d\n", checked_total)
    @printf("restricted graphs checked (minout >= %d): %d\n", minout_req, checked_restricted)
    @printf("restricted violations (Δ<0): %d\n", violations_restricted)

    if checked_restricted == 0
        println("No graphs satisfied the restriction (increase n or lower --minout).")
        return
    end

    @printf("Extremal over restricted family:\n")
    @printf("  min Δ(D) = %d   (Δ(D)=max_v(d2-d1); conjecture predicts Δ(D) >= 0)\n", min_Δ)
    @printf("  min R(D) = %.6f (R(D)=max_v(d2/d1) among vertices; conjecture would force R(D) >= 1 if applicable)\n", min_R)

    println("\n==== TOP-K MOST DANGEROUS IN RESTRICTED CLASS (ascending by (Δ, R, density)) ====")
    for (rank, item) in enumerate(topK)
        Δ, R, dens, min_out, max_out, dig = item
        @printf("\n#%d: Δ=%d | R=%.6f | density=%.4f | min_out=%d | max_out=%d\n",
                rank, Δ, R, dens, min_out, max_out)
        print(digits_to_edgelist(dig, pairs))
    end
end

main()
