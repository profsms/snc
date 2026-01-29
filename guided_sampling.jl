#!/usr/bin/env julia
# =============================================================================
# guided_sampling_paper.jl
#
# Guided heuristic search for near-extremal oriented graphs for the
# Second Neighborhood Conjecture (SNC) / square-degree doubling condition.
#
# Model:
#   An oriented graph on n labeled vertices is specified by choosing, for each
#   unordered pair {i,j}, either i→j, j→i, or no arc.
#
# Neighborhoods:
#   N1+(v) : out-neighborhood of v, size d1(v)
#   N2+(v) : NEW second out-neighborhood: vertices reachable by a directed path
#            v→u→w, excluding N1+(v) and excluding v itself, size d2(v)
#
# Conjecture-equivalent slack:
#   δ(v) := d2(v) - d1(v)
#   Δ(D) := max_v δ(v)
#
# The conjecture asserts: Δ(D) ≥ 0 for every oriented graph D.
# A counterexample would satisfy Δ(D) < 0.
#
# Objective:
#   Minimize Δ(D) using random restarts + simulated annealing on the edge-state
#   representation. The search returns the best (smallest) Δ found.
#
# Nontriviality restriction (recommended):
#   Require minimum outdegree δ+(D) ≥ minout (default minout=1),
#   so that sink-trivial satisfiers are not emphasized.
#
# Usage examples:
#   julia guided_sampling_paper.jl 9
#   julia guided_sampling_paper.jl 9 --restarts 50 --steps 20000 --p 0.55 --seed 1
#   julia guided_sampling_paper.jl 11 --restarts 100 --steps 50000 --p 0.45 --minout 1
#   julia guided_sampling_paper.jl 11 --out best.txt --log run.csv
#
# Output:
#   Prints an experiment summary and an edge list for the best-found instance.
# =============================================================================

using Printf
using Random

# -----------------------------------------------------------------------------
# Basic bitmask utilities (UInt64; requires n <= 63)
# -----------------------------------------------------------------------------
function bit(j::Int)::UInt64
    return UInt64(1) << (j - 1)
end

function popcount64(x::UInt64)::Int
    return count_ones(x)
end

function pairs_list(n::Int)
    pairs = Vector{Tuple{Int,Int}}()
    for i in 1:n-1, j in i+1:n
        push!(pairs, (i,j))
    end
    return pairs
end

# -----------------------------------------------------------------------------
# CLI parsing
# -----------------------------------------------------------------------------
function parse_args()
    n = nothing

    restarts = 50
    steps = 20_000
    p_edge = 0.5
    seed = 0
    report_every = 2_000

    # paper-quality: restrict away sink-trivial graphs
    minout = 1

    # optional files
    out_file = ""
    log_file = ""

    i = 1
    while i <= length(ARGS)
        arg = ARGS[i]
        if arg == "--restarts"
            restarts = parse(Int, ARGS[i+1]); i += 2
        elseif arg == "--steps"
            steps = parse(Int, ARGS[i+1]); i += 2
        elseif arg == "--p"
            p_edge = parse(Float64, ARGS[i+1]); i += 2
        elseif arg == "--seed"
            seed = parse(Int, ARGS[i+1]); i += 2
        elseif arg == "--report"
            report_every = parse(Int, ARGS[i+1]); i += 2
        elseif arg == "--minout"
            minout = parse(Int, ARGS[i+1]); i += 2
        elseif arg == "--out"
            out_file = ARGS[i+1]; i += 2
        elseif arg == "--log"
            log_file = ARGS[i+1]; i += 2
        else
            if n === nothing
                n = parse(Int, arg); i += 1
            else
                error("Unrecognized argument: $arg")
            end
        end
    end

    n === nothing && error("Provide n. Example: julia guided_sampling_paper.jl 9")
    return (n=n, restarts=restarts, steps=steps, p_edge=p_edge, seed=seed,
            report_every=report_every, minout=minout, out_file=out_file, log_file=log_file)
end

# -----------------------------------------------------------------------------
# Edge-state representation
# state[k] ∈ {0,1,2} for pair (i<j):
#   0: none, 1: i→j, 2: j→i
# outmask[v] is bitmask of out-neighbors of v
# -----------------------------------------------------------------------------
function apply_choice!(outmask::Vector{UInt64}, i::Int, j::Int, c::UInt8)
    if c == 0x00
        return
    elseif c == 0x01
        outmask[i] |= bit(j)
    elseif c == 0x02
        outmask[j] |= bit(i)
    else
        error("Invalid state value c=$c")
    end
end

function clear_choice!(outmask::Vector{UInt64}, i::Int, j::Int, c::UInt8)
    if c == 0x00
        return
    elseif c == 0x01
        outmask[i] &= ~bit(j)
    elseif c == 0x02
        outmask[j] &= ~bit(i)
    else
        error("Invalid state value c=$c")
    end
end

function build_outmask!(outmask::Vector{UInt64}, state::Vector{UInt8}, pairs)
    fill!(outmask, UInt64(0))
    for k in 1:length(pairs)
        (i,j) = pairs[k]
        apply_choice!(outmask, i, j, state[k])
    end
end

# Random graph initializer with density parameter p_edge
function random_state!(state::Vector{UInt8}, outmask::Vector{UInt64}, pairs,
                       p_edge::Float64, rng::AbstractRNG)
    fill!(outmask, UInt64(0))
    for k in 1:length(pairs)
        (i,j) = pairs[k]
        if rand(rng) < p_edge
            if rand(rng) < 0.5
                state[k] = 0x01
                outmask[i] |= bit(j)
            else
                state[k] = 0x02
                outmask[j] |= bit(i)
            end
        else
            state[k] = 0x00
        end
    end
end

# -----------------------------------------------------------------------------
# Diagnostics
# Compute Δ(D) = max_v(d2(v)-d1(v)) and the auxiliary ratio R(D)=max_v d2/d1 over d1>0
# Also compute outdegree statistics for restriction checks and reporting.
# -----------------------------------------------------------------------------
function degree_stats(outmask::Vector{UInt64}, n::Int)
    min_out = typemax(Int)
    max_out = 0
    m_edges = 0
    for v in 1:n
        dv = popcount64(outmask[v])
        m_edges += dv
        if dv < min_out
            min_out = dv
        end
        if dv > max_out
            max_out = dv
        end
    end
    return min_out, max_out, m_edges
end

function d2_exact(outmask::Vector{UInt64}, v::Int)
    N1 = outmask[v]
    d1 = popcount64(N1)
    if d1 == 0
        return 0, 0
    end

    # union of out-neighborhoods of out-neighbors
    N2raw = UInt64(0)
    tmp = N1
    while tmp != 0
        lowbit = tmp & (~tmp + 1)
        u = trailing_zeros(lowbit) + 1
        N2raw |= outmask[u]
        tmp &= tmp - 1
    end

    # new second neighbors: exclude N1 and v itself
    N2 = (N2raw & ~N1) & ~bit(v)
    d2 = popcount64(N2)
    return d2, d1
end

function metrics(outmask::Vector{UInt64}, n::Int)
    Δ = -typemax(Int)
    R = 0.0
    argmax = 1

    for v in 1:n
        d2, d1 = d2_exact(outmask, v)
        if d1 == 0
            # If sinks exist, they contribute margin 0; restriction usually avoids this.
            if 0 > Δ
                Δ = 0
                argmax = v
            end
            continue
        end

        margin = d2 - d1
        if margin > Δ
            Δ = margin
            argmax = v
        end

        ratio = d2 / d1
        if ratio > R
            R = ratio
        end
    end

    return Δ, R, argmax
end

# -----------------------------------------------------------------------------
# Output helpers
# -----------------------------------------------------------------------------
function state_to_edgelist(state::Vector{UInt8}, pairs)
    buf = IOBuffer()
    for k in 1:length(pairs)
        (i,j) = pairs[k]
        c = state[k]
        if c == 0x01
            @printf(buf, "%d -> %d\n", i, j)
        elseif c == 0x02
            @printf(buf, "%d -> %d\n", j, i)
        end
    end
    return String(take!(buf))
end

function maybe_write_text(path::String, txt::String)
    if isempty(path)
        return
    end
    open(path, "w") do io
        write(io, txt)
    end
end

function maybe_init_log(path::String)
    if isempty(path)
        return
    end
    # CSV header (simple, no dependencies)
    open(path, "w") do io
        println(io, "restart,step,accepted,Delta_current,Delta_best_restart,Delta_best_global,R_current,density,min_out,max_out")
    end
end

function maybe_log_row(path::String, restart::Int, step::Int, accepted::Bool,
                       Δcur::Int, Δbest_r::Int, Δbest_g::Int, Rcur::Float64,
                       density::Float64, min_out::Int, max_out::Int)
    if isempty(path)
        return
    end
    open(path, "a") do io
        @printf(io, "%d,%d,%d,%d,%d,%d,%.6f,%.6f,%d,%d\n",
                restart, step, accepted ? 1 : 0, Δcur, Δbest_r, Δbest_g, Rcur, density, min_out, max_out)
    end
end

# -----------------------------------------------------------------------------
# Simulated annealing / hill-climbing search
# Move: pick random pair and change its state to one of the other two values.
# Acceptance:
#   always if improves Δ (i.e., decreases it),
#   otherwise with probability exp(-ΔE/T) where ΔE = newΔ - curΔ > 0.
# Temperature schedule: linear from T0 to Tend.
# -----------------------------------------------------------------------------
function guided_search(n::Int; restarts::Int, steps::Int, p_edge::Float64, seed::Int,
                       report_every::Int, minout::Int, out_file::String, log_file::String)

    n > 63 && error("Bitmask approach requires n <= 63")

    rng = (seed == 0) ? Random.default_rng() : MersenneTwister(seed)
    pairs = pairs_list(n)
    m = length(pairs)

    outmask = fill(UInt64(0), n)
    state = fill(UInt8(0), m)

    best_global_Δ = typemax(Int)
    best_global_R = Inf
    best_global_state = copy(state)

    maybe_init_log(log_file)

    # Annealing parameters (can be exposed if needed)
    T0 = 2.0
    Tend = 0.05

    for r in 1:restarts
        # Initialize until restriction is satisfied (bounded tries to avoid infinite loops)
        tries = 0
        while true
            tries += 1
            random_state!(state, outmask, pairs, p_edge, rng)
            min_out, _, _ = degree_stats(outmask, n)
            if min_out >= minout
                break
            end
            if tries > 2000
                error("Could not sample an initial graph satisfying minout >= $minout. Try lowering --minout or increasing --p.")
            end
        end

        cur_Δ, cur_R, _ = metrics(outmask, n)
        min_out, max_out, m_edges = degree_stats(outmask, n)
        density = m_edges / (n*(n-1))

        best_restart_Δ = cur_Δ
        best_restart_state = copy(state)

        if cur_Δ < best_global_Δ
            best_global_Δ = cur_Δ
            best_global_R = cur_R
            best_global_state = copy(state)
        end

        for t in 1:steps
            # Linear temperature schedule
            α = (t-1) / max(1, steps-1)
            T = T0*(1-α) + Tend*α

            # Propose a local move
            k = rand(rng, 1:m)
            (i,j) = pairs[k]
            oldc = state[k]

            newc = oldc
            while newc == oldc
                newc = UInt8(rand(rng, 0:2))
            end

            # Apply
            clear_choice!(outmask, i, j, oldc)
            apply_choice!(outmask, i, j, newc)
            state[k] = newc

            # Enforce restriction cheaply: if violated, reject immediately
            min_out2, max_out2, m_edges2 = degree_stats(outmask, n)
            accepted = false
            new_Δ = cur_Δ
            new_R = cur_R

            if min_out2 >= minout
                new_Δ, new_R, _ = metrics(outmask, n)

                ΔE = new_Δ - cur_Δ  # we minimize Δ
                if ΔE <= 0
                    accepted = true
                else
                    pacc = exp(-Float64(ΔE)/T)
                    accepted = (rand(rng) < pacc)
                end
            end

            if accepted
                cur_Δ = new_Δ
                cur_R = new_R
                min_out = min_out2
                max_out = max_out2
                m_edges = m_edges2
                density = m_edges / (n*(n-1))

                if cur_Δ < best_restart_Δ
                    best_restart_Δ = cur_Δ
                    best_restart_state = copy(state)
                end
                if cur_Δ < best_global_Δ
                    best_global_Δ = cur_Δ
                    best_global_R = cur_R
                    best_global_state = copy(state)
                end
            else
                # Revert
                clear_choice!(outmask, i, j, newc)
                apply_choice!(outmask, i, j, oldc)
                state[k] = oldc
            end

            maybe_log_row(log_file, r, t, accepted,
                          cur_Δ, best_restart_Δ, best_global_Δ, cur_R, density, min_out, max_out)

            if report_every > 0 && (t % report_every == 0)
                @printf("restart %d/%d | step %d/%d | Δcur=%d | Δbest_r=%d | Δbest_g=%d | dens=%.3f | minout=%d\n",
                        r, restarts, t, steps, cur_Δ, best_restart_Δ, best_global_Δ, density, min_out)
            end

            # Early stop if a genuine counterexample is found
            if cur_Δ < 0
                println("\nFOUND COUNTEREXAMPLE CANDIDATE (Δ < 0)")
                println("Δ(D) = ", cur_Δ, "   (recall: conjecture predicts Δ(D) ≥ 0)")
                println("R(D) = ", @sprintf("%.6f", cur_R))
                edgelist = state_to_edgelist(state, pairs)
                println(edgelist)
                maybe_write_text(out_file, edgelist)
                return (bestΔ=cur_Δ, bestR=cur_R, state=copy(state), pairs=pairs)
            end
        end

        # For paper-quality reporting: summarize each restart
        @printf("== end restart %d/%d: best_restart_Δ=%d | best_global_Δ=%d ==\n",
                r, restarts, best_restart_Δ, best_global_Δ)

        # Restore best restart state into current to avoid keeping stale state in memory
        # (not required, but keeps invariants easy to reason about)
        state = copy(best_restart_state)
        build_outmask!(outmask, state, pairs)
    end

    # final output
    build_outmask!(outmask, best_global_state, pairs)
    best_global_Δ, best_global_R, _ = metrics(outmask, n)

    edgelist = state_to_edgelist(best_global_state, pairs)
    maybe_write_text(out_file, edgelist)

    return (bestΔ=best_global_Δ, bestR=best_global_R, state=best_global_state, pairs=pairs)
end

# -----------------------------------------------------------------------------
# Main
# -----------------------------------------------------------------------------
function main()
    args = parse_args()
    n = args.n

    if n < 2
        error("Need n >= 2.")
    end
    if n > 63
        error("Need n <= 63 for UInt64 bitmasks.")
    end

    println("==== Guided SNC Search (paper-quality run record) ====")
    @printf("n=%d | restarts=%d | steps=%d | p=%.3f | minout=%d | seed=%d\n",
            n, args.restarts, args.steps, args.p_edge, args.minout, args.seed)
    if !isempty(args.out_file)
        @printf("writing best edge list to: %s\n", args.out_file)
    end
    if !isempty(args.log_file)
        @printf("logging trajectory to: %s\n", args.log_file)
    end
    println("Objective: minimize Δ(D)=max_v(|N2^+(v)|-|N1^+(v)|). Counterexample iff Δ(D)<0.")
    println("------------------------------------------------------")

    res = guided_search(n;
        restarts=args.restarts,
        steps=args.steps,
        p_edge=args.p_edge,
        seed=args.seed,
        report_every=args.report_every,
        minout=args.minout,
        out_file=args.out_file,
        log_file=args.log_file
    )

    println("\n==== BEST FOUND INSTANCE ====")
    @printf("best Δ(D) = %d   (counterexample would require < 0)\n", res.bestΔ)
    @printf("best R(D) = %.6f (R(D)=max_v d2(v)/d1(v) over d1(v)>0)\n", res.bestR)
    println("\nEdge list:")
    println(state_to_edgelist(res.state, res.pairs))
end

main()
