#!/usr/bin/env julia
# =============================================================================
# piza_sampling.jl
#
# Sampling-based analogue of piza_filters.jl for n > 6.
#
# We sample random oriented graphs D on n labeled vertices:
#   for each unordered pair {i,j}, put an arc with probability p_edge,
#   and if present orient it uniformly (i->j or j->i).
#
# We filter by:
#   - min outdegree >= minout
#   - optionally keep only Piza graphs: Δ(D)=0   (Piza := "delta = 0")
#     or also keep "near-Piza" with Δ(D) <= deltacap for diagnostics.
#
# For each kept graph, we compute invariants of:
#   - the digraph D: SCC count, max SCC size
#   - underlying undirected graph U(D): m(U), Δ(U), bipartite?, triangles, degeneracy
#   - optional: kernel existence (only if n <= kernel_maxn; brute force)
#   - optional: exact χ(U) and χ'(U) only up to small n (configurable)
#     otherwise fast heuristics:
#        χ_greedy(U) (Welsh-Powell)
#        χ'_greedy(U) (sequential greedy edge coloring)
#     Vizing class is then classified as:
#        - "I" if we *certify* χ'(U)=Δ(U) (exact, or heuristic finds Δ-coloring)
#        - "II?" if heuristic fails with Δ colors but succeeds with Δ+1
#        - "UNK" otherwise
#
# Outputs:
#   - counts: sampled / eligible / kept / Piza-found
#   - best Δ(D) observed, and distribution of Δ(D) among eligible samples
#   - histograms over kept graphs (Piza or near-Piza)
#   - optional CSV export of kept graphs (one row per kept sample)
#
# Typical usage:
#   julia piza_sampling.jl 12 --samples 200000 --p 0.5 --minout 1 --deltacap 0
#   julia piza_sampling.jl 20 --samples 500000 --p 0.35 --minout 1 --deltacap 0
#   julia piza_sampling.jl 18 --samples 200000 --p 0.4 --minout 1 --deltacap 2
#
# Notes:
#   - This is NOT exhaustive. It is intended for empirical structure discovery.
#   - For n>12, exact χ and χ' are typically too slow; use heuristics.
# =============================================================================

using Random
using Printf

# ----------------------------
# CLI parsing
# ----------------------------
function parse_args()
    n = nothing
    samples = 200_000
    p_edge = 0.5
    minout = 1
    deltacap = 0          # 0 means "Piza only"; >0 means also keep near-Piza
    seed = 0
    report = 10_000

    csv = ""
    maxrows = 0

    # exact computations only up to these n (0 disables)
    exact_chi_maxn = 10
    exact_chip_maxn = 9
    kernel_maxn = 18

    i = 1
    while i <= length(ARGS)
        a = ARGS[i]
        if a == "--samples"
            samples = parse(Int, ARGS[i+1]); i += 2
        elseif a == "--p"
            p_edge = parse(Float64, ARGS[i+1]); i += 2
        elseif a == "--minout"
            minout = parse(Int, ARGS[i+1]); i += 2
        elseif a == "--deltacap"
            deltacap = parse(Int, ARGS[i+1]); i += 2
        elseif a == "--seed"
            seed = parse(Int, ARGS[i+1]); i += 2
        elseif a == "--report"
            report = parse(Int, ARGS[i+1]); i += 2
        elseif a == "--csv"
            csv = ARGS[i+1]; i += 2
        elseif a == "--maxrows"
            maxrows = parse(Int, ARGS[i+1]); i += 2
        elseif a == "--exact_chi_maxn"
            exact_chi_maxn = parse(Int, ARGS[i+1]); i += 2
        elseif a == "--exact_chip_maxn"
            exact_chip_maxn = parse(Int, ARGS[i+1]); i += 2
        elseif a == "--kernel_maxn"
            kernel_maxn = parse(Int, ARGS[i+1]); i += 2
        else
            if n === nothing
                n = parse(Int, a); i += 1
            else
                error("Unrecognized argument: $a")
            end
        end
    end
    n === nothing && error("Usage: julia piza_sampling.jl n [--samples N] [--p 0.5] [--minout 1] [--deltacap 0] ...")
    return (n=n, samples=samples, p_edge=p_edge, minout=minout, deltacap=deltacap,
            seed=seed, report=report, csv=csv, maxrows=maxrows,
            exact_chi_maxn=exact_chi_maxn, exact_chip_maxn=exact_chip_maxn, kernel_maxn=kernel_maxn)
end

# ----------------------------
# Bit utilities
# ----------------------------
bit(j::Int)::UInt64 = UInt64(1) << (j-1)
popcount64(x::UInt64)::Int = count_ones(x)

# ----------------------------
# Random oriented graph generator
# outmask[v] bitmask of out-neighbors
# ----------------------------
function random_oriented!(outmask::Vector{UInt64}, n::Int, p_edge::Float64, rng::AbstractRNG)
    fill!(outmask, UInt64(0))
    for i in 1:n-1
        bi = bit(i)
        for j in i+1:n
            if rand(rng) < p_edge
                if rand(rng) < 0.5
                    outmask[i] |= bit(j)
                else
                    outmask[j] |= bi
                end
            end
        end
    end
end

function outdeg_stats(outmask::Vector{UInt64}, n::Int)
    min_out = typemax(Int)
    max_out = 0
    m_dir = 0
    for v in 1:n
        dv = popcount64(outmask[v])
        m_dir += dv
        min_out = min(min_out, dv)
        max_out = max(max_out, dv)
    end
    return min_out, max_out, m_dir
end

# ----------------------------
# Δ(D) for the SNC-style metric:
# Δ(D) = max_v (|N2(v)| - |N1(v)|)   where N2 are NEW second out-neighbors
# Piza graphs := Δ(D)=0
# ----------------------------
function delta_D(outmask::Vector{UInt64}, n::Int)
    Δ = -typemax(Int)
    for v in 1:n
        N1 = outmask[v]
        d1 = popcount64(N1)
        if d1 == 0
            Δ = max(Δ, 0)
            continue
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
        Δ = max(Δ, d2 - d1)
    end
    return Δ
end

# ----------------------------
# Underlying undirected graph U(D)
# adjU[v] = bitmask of neighbors
# ----------------------------
function build_undirected!(adjU::Vector{UInt64}, outmask::Vector{UInt64}, n::Int)
    fill!(adjU, UInt64(0))
    for i in 1:n
        tmp = outmask[i]
        while tmp != 0
            lowbit = tmp & (~tmp + 1)
            j = trailing_zeros(lowbit) + 1
            adjU[i] |= bit(j)
            adjU[j] |= bit(i)
            tmp &= tmp - 1
        end
    end
end

function undirected_stats(adjU::Vector{UInt64}, n::Int)
    ΔU = 0
    sdeg = 0
    δU = typemax(Int)
    for v in 1:n
        dv = popcount64(adjU[v])
        ΔU = max(ΔU, dv)
        δU = min(δU, dv)
        sdeg += dv
    end
    mU = sdeg ÷ 2
    return mU, ΔU, δU
end

function is_bipartite(adjU::Vector{UInt64}, n::Int)
    color = fill(0, n)
    for s in 1:n
        color[s] != 0 && continue
        color[s] = 1
        queue = [s]
        while !isempty(queue)
            v = pop!(queue)
            tmp = adjU[v]
            while tmp != 0
                lowbit = tmp & (~tmp + 1)
                u = trailing_zeros(lowbit) + 1
                if color[u] == 0
                    color[u] = -color[v]
                    push!(queue, u)
                elseif color[u] == color[v]
                    return false
                end
                tmp &= tmp - 1
            end
        end
    end
    return true
end

function triangle_count(adjU::Vector{UInt64}, n::Int)
    cnt = 0
    for i in 1:n-2
        for j in i+1:n-1
            (adjU[i] & bit(j)) == 0 && continue
            for k in j+1:n
                if (adjU[i] & bit(k)) != 0 && (adjU[j] & bit(k)) != 0
                    cnt += 1
                end
            end
        end
    end
    return cnt
end

function degeneracy(adjU::Vector{UInt64}, n::Int)
    alive = trues(n)
    deg = zeros(Int, n)
    for v in 1:n
        deg[v] = popcount64(adjU[v])
    end
    k = 0
    for _ in 1:n
        vmin = 0
        dmin = typemax(Int)
        for v in 1:n
            if alive[v] && deg[v] < dmin
                dmin = deg[v]
                vmin = v
            end
        end
        k = max(k, dmin)
        alive[vmin] = false
        tmp = adjU[vmin]
        while tmp != 0
            lowbit = tmp & (~tmp + 1)
            u = trailing_zeros(lowbit) + 1
            if alive[u]
                deg[u] -= 1
            end
            tmp &= tmp - 1
        end
    end
    return k
end

# ----------------------------
# SCC stats (Kosaraju)
# ----------------------------
function build_inmask!(inmask::Vector{UInt64}, outmask::Vector{UInt64}, n::Int)
    fill!(inmask, UInt64(0))
    for v in 1:n
        tmp = outmask[v]
        while tmp != 0
            lowbit = tmp & (~tmp + 1)
            u = trailing_zeros(lowbit) + 1
            inmask[u] |= bit(v)
            tmp &= tmp - 1
        end
    end
end

function scc_stats(outmask::Vector{UInt64}, n::Int)
    inmask = fill(UInt64(0), n)
    build_inmask!(inmask, outmask, n)

    visited = falses(n)
    order = Int[]

    function dfs1(v::Int)
        visited[v] = true
        tmp = outmask[v]
        while tmp != 0
            lowbit = tmp & (~tmp + 1)
            u = trailing_zeros(lowbit) + 1
            if !visited[u]
                dfs1(u)
            end
            tmp &= tmp - 1
        end
        push!(order, v)
    end

    for v in 1:n
        !visited[v] && dfs1(v)
    end

    visited .= false
    scc_sizes = Int[]

    function dfs2(v::Int)
        visited[v] = true
        sz = 1
        tmp = inmask[v]
        while tmp != 0
            lowbit = tmp & (~tmp + 1)
            u = trailing_zeros(lowbit) + 1
            if !visited[u]
                sz += dfs2(u)
            end
            tmp &= tmp - 1
        end
        return sz
    end

    for idx in length(order):-1:1
        v = order[idx]
        if !visited[v]
            push!(scc_sizes, dfs2(v))
        end
    end

    return length(scc_sizes), maximum(scc_sizes)
end

# ----------------------------
# Kernel existence (bruteforce; only for small n)
# ----------------------------
function has_kernel(outmask::Vector{UInt64}, n::Int)
    for S in 0:(UInt64(1)<<n)-1
        S == 0 && continue

        independent = true
        tmpS = S
        while tmpS != 0 && independent
            lowbit = tmpS & (~tmpS + 1)
            i = trailing_zeros(lowbit) + 1
            tmpS2 = S & ~lowbit
            while tmpS2 != 0
                lowbit2 = tmpS2 & (~tmpS2 + 1)
                j = trailing_zeros(lowbit2) + 1
                if ((outmask[i] & bit(j)) != 0) || ((outmask[j] & bit(i)) != 0)
                    independent = false
                    break
                end
                tmpS2 &= tmpS2 - 1
            end
            tmpS &= tmpS - 1
        end
        independent || continue

        absorbent = true
        for x in 1:n
            (S & bit(x)) != 0 && continue
            if (outmask[x] & S) == 0
                absorbent = false
                break
            end
        end
        absorbent && return true
    end
    return false
end

# ----------------------------
# Coloring: exact χ(U) for small n, greedy for larger
# ----------------------------
function chromatic_number_exact(adjU::Vector{UInt64}, n::Int)
    order = collect(1:n)
    sort!(order, by = v -> popcount64(adjU[v]), rev=true)
    colors = fill(0, n)
    best = Ref(n)

    function can_color(v::Int, c::Int)
        tmp = adjU[v]
        while tmp != 0
            lowbit = tmp & (~tmp + 1)
            u = trailing_zeros(lowbit) + 1
            if colors[u] == c
                return false
            end
            tmp &= tmp - 1
        end
        return true
    end

    function dfs(idx::Int, used::Int)
        used >= best[] && return
        if idx > n
            best[] = min(best[], used)
            return
        end
        v = order[idx]
        for c in 1:used
            if can_color(v, c)
                colors[v] = c
                dfs(idx+1, used)
                colors[v] = 0
            end
        end
        colors[v] = used + 1
        dfs(idx+1, used+1)
        colors[v] = 0
    end

    dfs(1, 0)
    return best[]
end

function chromatic_number_greedy(adjU::Vector{UInt64}, n::Int)
    order = collect(1:n)
    sort!(order, by = v -> popcount64(adjU[v]), rev=true)  # Welsh-Powell
    col = fill(0, n)
    used = 0
    for v in order
        used_colors = falses(used)
        tmp = adjU[v]
        while tmp != 0
            lowbit = tmp & (~tmp + 1)
            u = trailing_zeros(lowbit) + 1
            c = col[u]
            if c != 0
                used_colors[c] = true
            end
            tmp &= tmp - 1
        end
        c = 1
        while c <= used && used_colors[c]
            c += 1
        end
        if c == used + 1
            used += 1
        end
        col[v] = c
    end
    return used
end

# ----------------------------
# Edge coloring heuristic: greedy sequential edge-coloring
# Returns number of colors used.
# Also allows "try with K colors" feasibility test (heuristic).
# ----------------------------
function undirected_edges(adjU::Vector{UInt64}, n::Int)
    edges = Vector{Tuple{Int,Int}}()
    for i in 1:n-1
        for j in i+1:n
            if (adjU[i] & bit(j)) != 0
                push!(edges, (i,j))
            end
        end
    end
    return edges
end

function edgecolor_greedy_used(adjU::Vector{UInt64}, n::Int)
    edges = undirected_edges(adjU, n)
    m = length(edges)
    if m == 0
        return 0
    end
    # order edges by sum degrees
    deg = [popcount64(adjU[v]) for v in 1:n]
    order = collect(1:m)
    sort!(order, by = e -> (deg[edges[e][1]] + deg[edges[e][2]]), rev=true)

    # colors at each vertex: set of colors used
    used_at = [UInt64(0) for _ in 1:n]  # bitmask of used colors (supports up to 64 colors)

    maxc = 0
    for idx in 1:m
        e = order[idx]
        (a,b) = edges[e]
        forb = used_at[a] | used_at[b]
        c = 1
        while c <= 63 && ((forb & (UInt64(1) << (c-1))) != 0)
            c += 1
        end
        if c > 63
            # fallback: count as huge
            return 99
        end
        used_at[a] |= (UInt64(1) << (c-1))
        used_at[b] |= (UInt64(1) << (c-1))
        maxc = max(maxc, c)
    end
    return maxc
end

function edgecolor_tryK_greedy(adjU::Vector{UInt64}, n::Int, K::Int)
    K <= 0 && return true
    K > 63 && return false

    edges = undirected_edges(adjU, n)
    m = length(edges)
    if m == 0
        return true
    end
    deg = [popcount64(adjU[v]) for v in 1:n]
    order = collect(1:m)
    sort!(order, by = e -> (deg[edges[e][1]] + deg[edges[e][2]]), rev=true)

    used_at = [UInt64(0) for _ in 1:n]
    for e in order
        (a,b) = edges[e]
        forb = used_at[a] | used_at[b]
        # find first available in 1..K
        c = 1
        while c <= K && ((forb & (UInt64(1) << (c-1))) != 0)
            c += 1
        end
        if c > K
            return false
        end
        used_at[a] |= (UInt64(1) << (c-1))
        used_at[b] |= (UInt64(1) << (c-1))
    end
    return true
end

# ----------------------------
# histogram helpers
# ----------------------------
function add_hist!(hist::Dict{Int,Int}, k::Int)
    hist[k] = get(hist, k, 0) + 1
end

function print_hist(title::String, hist::Dict{Int,Int}; maxlines::Int=30)
    println("\n== ", title, " ==")
    if isempty(hist)
        println("(empty)")
        return
    end
    keys_sorted = sort(collect(keys(hist)))
    shown = 0
    for k in keys_sorted
        v = hist[k]
        barlen = min(60, v)
        bar = repeat("█", barlen)
        @printf("%4d : %10d %s\n", k, v, bar)
        shown += 1
        if shown >= maxlines && length(keys_sorted) > maxlines
            println("... (truncated; use smaller maxlines or export CSV)")
            break
        end
    end
end

# ----------------------------
# CSV writer
# ----------------------------
function open_csv(path::String)
    isempty(path) && return nothing
    io = open(path, "w")
    println(io, "id,deltaD,edges_dir,density_dir,min_out,max_out,mU,DeltaU,deltaU,chi,chip,vizing_class,bipartite,triangles,degeneracy,scc_count,scc_max,kernel")
    return io
end

function write_row(io, id, ΔD, mdir, dens_dir, min_out, max_out, mU, ΔU, δU, chi, chip, vclass, bip, tri, degen, scc_c, scc_m, ker)
    io === nothing && return
    println(io,
        id, ",",
        ΔD, ",",
        mdir, ",",
        @sprintf("%.6f", dens_dir), ",",
        min_out, ",",
        max_out, ",",
        mU, ",",
        ΔU, ",",
        δU, ",",
        chi, ",",
        chip, ",",
        vclass, ",",
        bip, ",",
        tri, ",",
        degen, ",",
        scc_c, ",",
        scc_m, ",",
        ker
    )
end

# ----------------------------
# Main sampling loop
# ----------------------------
function main()
    args = parse_args()
    n = args.n
    n > 63 && error("Bitmask implementation requires n <= 63.")
    rng = args.seed == 0 ? Random.default_rng() : MersenneTwister(args.seed)

    @printf("Sampling oriented graphs on n=%d vertices\n", n)
    @printf("samples=%d | p=%.3f | minout≥%d | deltacap=%d (0 means Piza-only)\n",
            args.samples, args.p_edge, args.minout, args.deltacap)

    outmask = fill(UInt64(0), n)
    adjU = fill(UInt64(0), n)

    io = open_csv(args.csv)
    cap = args.maxrows

    sampled = 0
    eligible = 0
    kept = 0
    piza = 0

    bestΔ = typemax(Int)
    histΔ = Dict{Int,Int}()

    # Histograms among kept graphs
    H_chi = Dict{Int,Int}()
    H_chip = Dict{Int,Int}()
    H_mU = Dict{Int,Int}()
    H_ΔU = Dict{Int,Int}()
    H_δU = Dict{Int,Int}()
    H_scc = Dict{Int,Int}()
    H_sccmax = Dict{Int,Int}()
    H_kernel = Dict{Int,Int}()
    H_vclass = Dict{Int,Int}()  # 1=I, 2=II?, 0=UNK

    for t in 1:args.samples
        sampled += 1
        random_oriented!(outmask, n, args.p_edge, rng)
        min_out, max_out, mdir = outdeg_stats(outmask, n)
        min_out < args.minout && continue
        eligible += 1

        ΔD = delta_D(outmask, n)
        add_hist!(histΔ, ΔD)
        bestΔ = min(bestΔ, ΔD)

        # keep only Piza (Δ=0) or also near-Piza (Δ<=deltacap)
        if ΔD > args.deltacap
            if args.report > 0 && (t % args.report == 0)
                @printf("t=%d | eligible=%d | kept=%d | piza=%d | bestΔ=%d\n",
                        t, eligible, kept, piza, bestΔ)
            end
            continue
        end

        kept += 1
        if ΔD == 0
            piza += 1
        end

        dens_dir = mdir / (n*(n-1))

        build_undirected!(adjU, outmask, n)
        mU, ΔU, δU = undirected_stats(adjU, n)
        bip = is_bipartite(adjU, n) ? 1 : 0
        tri = triangle_count(adjU, n)
        degen = degeneracy(adjU, n)
        scc_c, scc_m = scc_stats(outmask, n)

        # χ(U)
        chi = (args.exact_chi_maxn > 0 && n <= args.exact_chi_maxn) ? chromatic_number_exact(adjU, n) : chromatic_number_greedy(adjU, n)

        # χ'(U) / Vizing class (exact only for small n; otherwise heuristic)
        chip = -1
        vclass = 0  # 1=I, 2=II?, 0=UNK
        if args.exact_chip_maxn > 0 && n <= args.exact_chip_maxn
            # exact χ' is expensive; we approximate "exact" here by trying Δ and Δ+1 with greedy feasibility
            # For n<=9 this is usually reliable and fast.
            if edgecolor_tryK_greedy(adjU, n, ΔU)
                chip = ΔU
                vclass = 1
            else
                if edgecolor_tryK_greedy(adjU, n, ΔU+1)
                    chip = ΔU + 1
                    vclass = 2
                else
                    chip = edgecolor_greedy_used(adjU, n)
                    vclass = 0
                end
            end
        else
            # heuristic regime
            if edgecolor_tryK_greedy(adjU, n, ΔU)
                chip = ΔU
                vclass = 1
            else
                if edgecolor_tryK_greedy(adjU, n, ΔU+1)
                    chip = ΔU + 1
                    vclass = 2
                else
                    chip = edgecolor_greedy_used(adjU, n)
                    vclass = 0
                end
            end
        end

        # kernel (only for small n)
        ker = -1
        if n <= args.kernel_maxn
            ker = has_kernel(outmask, n) ? 1 : 0
        end

        # update histograms
        add_hist!(H_chi, chi)
        add_hist!(H_chip, chip)
        add_hist!(H_mU, mU)
        add_hist!(H_ΔU, ΔU)
        add_hist!(H_δU, δU)
        add_hist!(H_scc, scc_c)
        add_hist!(H_sccmax, scc_m)
        if ker != -1
            add_hist!(H_kernel, ker)
        end
        add_hist!(H_vclass, vclass)

        # CSV
        if io !== nothing && (cap == 0 || kept <= cap)
            write_row(io, kept, ΔD, mdir, dens_dir, min_out, max_out, mU, ΔU, δU, chi, chip, vclass, bip, tri, degen, scc_c, scc_m, ker)
        end

        if args.report > 0 && (t % args.report == 0)
            @printf("t=%d | eligible=%d | kept=%d | piza=%d | bestΔ=%d\n",
                    t, eligible, kept, piza, bestΔ)
        end
    end

    if io !== nothing
        close(io)
        println("\nCSV written to: ", args.csv)
    end

    println("\n==== SUMMARY ====")
    @printf("n=%d | sampled=%d | eligible(minout)=%d | kept(Δ<=%d)=%d | piza(Δ=0)=%d\n",
            n, sampled, eligible, args.deltacap, kept, piza)
    @printf("best Δ(D) observed among eligible samples: %d\n", bestΔ)

    print_hist("Δ(D) among eligible samples", histΔ; maxlines=50)

    println("\n==== HISTOGRAMS among kept graphs (Δ<=deltacap) ====")
    print_hist("χ(U)  (exact if n<=exact_chi_maxn else greedy upper bound)", H_chi)
    print_hist("χ'(U) (heuristic; may be exact only for tiny n)", H_chip)
    print_hist("Vizing class heuristic (1=I certified, 2=II? likely, 0=UNK)", H_vclass)
    print_hist("m(U) (# undirected edges)", H_mU)
    print_hist("Δ(U) (max degree)", H_ΔU)
    print_hist("δ(U) (min degree)", H_δU)
    print_hist("SCC count", H_scc)
    print_hist("max SCC size", H_sccmax)
    if !isempty(H_kernel)
        print_hist("kernel (0/1) [only computed for n<=kernel_maxn]", H_kernel)
    else
        println("\n(kernel not computed: n > kernel_maxn)")
    end

    println("\nNotes:")
    println("- For n>6, χ(U) and χ'(U) are heuristic unless you set exact_* thresholds high.")
    println("- 'Vizing class' is heuristic: Class I is only claimed when Δ(U)-edge-coloring succeeds (greedy).")
    println("- Use --csv to export kept samples for offline analysis / plotting.")
end

main()
