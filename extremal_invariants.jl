#!/usr/bin/env julia
# =============================================================================
# extremal_invariants_v2.jl
#
# Exhaustively enumerates oriented graphs on n labeled vertices (n<=6 recommended),
# filters to your "Piza graphs" (Δ(D)=0) with optional minout constraint,
# and computes richer diagnostics:
#
#   - Histograms: χ(U), χ'(U), SCC count, SCC max size, kernel (0/1),
#                 m(U) (undirected edges), Δ(U) (max degree in U)
#   - Summary fractions: strongly connected, has kernel, bipartite
#   - Vizing class counts among Piza graphs:
#       Class I  : χ'(U) = Δ(U)
#       Class II : χ'(U) = Δ(U)+1
#
# Underlying undirected graph U(D): edge {i,j} exists iff i→j or j→i in D.
#
# Usage:
#   julia extremal_invariants_v2.jl 6 --minout 1
#   julia extremal_invariants_v2.jl 6 --minout 1 --csv extremals6.csv --maxrows 50000
#
# Notes:
# - Counts are for labeled digraphs (no isomorphism reduction).
# - χ(U) computed exactly by backtracking (ok for n<=6).
# - χ'(U) computed exactly using Vizing bound (tries Δ(U) and Δ(U)+1).
# - Kernel existence brute-forced over subsets (feasible for n<=20, but enumeration dominates).
# =============================================================================

using Printf

# ----------------------------
# Bit utilities
# ----------------------------
bit(j::Int)::UInt64 = UInt64(1) << (j-1)
popcount64(x::UInt64)::Int = count_ones(x)

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

# digits[k] for pair (i<j):
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

# ----------------------------
# Directed Δ(D)
# ----------------------------
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

function delta_D(outmask::Vector{UInt64}, n::Int)
    Δ = -typemax(Int)
    for v in 1:n
        d2, d1 = d2_exact(outmask, v)
        if d1 == 0
            if 0 > Δ
                Δ = 0
            end
        else
            margin = d2 - d1
            if margin > Δ
                Δ = margin
            end
        end
    end
    return Δ
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
# Underlying undirected graph U(D): adjacency bitmasks adjU[v]
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

function undirected_stats(adjU::Vector{UInt64}, n::Int)
    # returns (m_U, ΔU, degrees vector)
    degs = Vector{Int}(undef, n)
    ΔU = 0
    sdeg = 0
    for v in 1:n
        dv = popcount64(adjU[v])
        degs[v] = dv
        ΔU = max(ΔU, dv)
        sdeg += dv
    end
    mU = sdeg ÷ 2
    return mU, ΔU, degs
end

# ----------------------------
# Invariants on U(D)
# ----------------------------
function is_bipartite(adjU::Vector{UInt64}, n::Int)
    color = fill(0, n) # 0 uncolored, ±1 colors
    for s in 1:n
        if color[s] != 0
            continue
        end
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
            if (adjU[i] & bit(j)) == 0
                continue
            end
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

# exact chromatic number χ(U) via backtracking
function chromatic_number(adjU::Vector{UInt64}, n::Int)
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
        if used >= best[]
            return
        end
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

# exact chromatic index χ'(U) for small n using Vizing bound: tries Δ(U), Δ(U)+1
function chromatic_index(adjU::Vector{UInt64}, n::Int)
    edges = undirected_edges(adjU, n)
    m = length(edges)
    if m == 0
        return 0
    end

    # max degree Δ(U)
    ΔU = 0
    for v in 1:n
        ΔU = max(ΔU, popcount64(adjU[v]))
    end

    # Edge conflict graph (bitmask over edges)
    conflict = [UInt64(0) for _ in 1:m]
    for e1 in 1:m
        (a,b) = edges[e1]
        mask = UInt64(0)
        for e2 in 1:m
            if e1 == e2; continue; end
            (c,d) = edges[e2]
            if a==c || a==d || b==c || b==d
                mask |= UInt64(1) << (e2-1)
            end
        end
        conflict[e1] = mask
    end

    # order edges by descending conflict degree
    order = collect(1:m)
    sort!(order, by = e -> popcount64(conflict[e]), rev=true)

    edgecolor = fill(0, m)

    function feasible(K::Int)
        function dfs(idx::Int)
            if idx > m
                return true
            end
            e = order[idx]
            used = falses(K)
            tmp = conflict[e]
            while tmp != 0
                lowbit = tmp & (~tmp + 1)
                e2 = trailing_zeros(lowbit) + 1
                c = edgecolor[e2]
                if c != 0
                    used[c] = true
                end
                tmp &= tmp - 1
            end
            for c in 1:K
                if !used[c]
                    edgecolor[e] = c
                    if dfs(idx+1)
                        return true
                    end
                    edgecolor[e] = 0
                end
            end
            return false
        end
        fill!(edgecolor, 0)
        return dfs(1)
    end

    if feasible(ΔU)
        return ΔU
    else
        return ΔU + 1
    end
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
        if !visited[v]
            dfs1(v)
        end
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
# Kernel existence in digraph (bruteforce subsets)
# Kernel = independent + absorbent
# independent: no arcs between any two vertices in K (either direction)
# absorbent: for every x∉K, exists y∈K with x→y
# ----------------------------
function has_kernel(outmask::Vector{UInt64}, n::Int)
    for S in 0:(UInt64(1)<<n)-1
        if S == 0
            continue
        end

        # independence
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
        if !independent
            continue
        end

        # absorbent
        absorbent = true
        for x in 1:n
            if (S & bit(x)) != 0
                continue
            end
            if (outmask[x] & S) == 0
                absorbent = false
                break
            end
        end
        if absorbent
            return true
        end
    end
    return false
end

# ----------------------------
# Pretty histogram printer
# ----------------------------
function print_hist(title::String, hist::Dict{Int,Int})
    println("\n== ", title, " ==")
    if isempty(hist)
        println("(empty)")
        return
    end
    keys_sorted = sort(collect(keys(hist)))
    for k in keys_sorted
        v = hist[k]
        barlen = min(60, v)
        bar = repeat("█", barlen)
        @printf("%3d : %8d %s\n", k, v, bar)
    end
end

# ----------------------------
# CLI
# ----------------------------
function parse_args()
    n = nothing
    minout = 1
    progress = 1_000_000
    csvfile = ""
    maxrows = 0
    topsig = 30

    i = 1
    while i <= length(ARGS)
        arg = ARGS[i]
        if arg == "--minout"
            minout = parse(Int, ARGS[i+1]); i += 2
        elseif arg == "--progress"
            progress = parse(Int, ARGS[i+1]); i += 2
        elseif arg == "--csv"
            csvfile = ARGS[i+1]; i += 2
        elseif arg == "--maxrows"
            maxrows = parse(Int, ARGS[i+1]); i += 2
        elseif arg == "--topsig"
            topsig = parse(Int, ARGS[i+1]); i += 2
        else
            if n === nothing
                n = parse(Int, arg); i += 1
            else
                error("Unrecognized argument: $arg")
            end
        end
    end

    n === nothing && error("Usage: julia extremal_invariants_v2.jl 6 [--minout 1] [--csv file.csv]")
    return (n=n, minout=minout, progress=progress, csvfile=csvfile, maxrows=maxrows, topsig=topsig)
end

# ----------------------------
# Main
# ----------------------------
function main()
    args = parse_args()
    n = args.n
    n > 63 && error("Requires n <= 63 (UInt64 bitmasks).")
    if n > 7
        @printf("WARNING: n=%d is likely infeasible for full enumeration on a laptop.\n", n)
    end

    pairs = pairs_list(n)
    m = length(pairs)
    total = big(3)^big(m)
    @printf("n=%d, pairs=%d, total oriented graphs = 3^%d = %s\n", n, m, m, string(total))
    @printf("Filtering: Piza graphs = (Δ(D)=0) and min outdegree >= %d\n", args.minout)

    digits = fill(UInt8(0), m)
    outmask = fill(UInt64(0), n)
    adjU = fill(UInt64(0), n)

    checked = 0
    kept = 0

    # histograms
    hist_chi      = Dict{Int,Int}()
    hist_chip     = Dict{Int,Int}()
    hist_scc_cnt  = Dict{Int,Int}()
    hist_scc_max  = Dict{Int,Int}()
    hist_kernel   = Dict{Int,Int}()  # 0/1
    hist_mU       = Dict{Int,Int}()
    hist_ΔU       = Dict{Int,Int}()

    # totals for fractions
    cnt_strong = 0
    cnt_kernel = 0
    cnt_bip    = 0

    # Vizing class counts among Piza graphs
    vizing_I = 0
    vizing_II = 0
    vizing_other = 0  # should remain 0 for simple graphs, but keep for sanity

    # signature counts
    # (chi, chi', bip, tri, degen, scc#, sccmax, kernel, minout, maxout)
    sigcount = Dict{NTuple{10,Int}, Int}()

    # optional CSV
    io = nothing
    if !isempty(args.csvfile)
        io = open(args.csvfile, "w")
        println(io, "id,edges_dir,density_dir,DeltaD,min_out,max_out,mU,DeltaU,chi,chi_index,vizing_class,bipartite,triangles,degeneracy,scc_count,scc_max,kernel")
    end
    rowcap = args.maxrows

    while true
        checked += 1
        build_outmask!(outmask, digits, pairs)

        min_out, max_out, mdir = outdeg_stats(outmask, n)
        if min_out < args.minout
            if !increment_base3!(digits); break; end
            continue
        end

        ΔD = delta_D(outmask, n)
        if ΔD != 0
            if !increment_base3!(digits); break; end
            continue
        end

        # This is a Piza graph
        kept += 1
        dens_dir = mdir / (n*(n-1))

        # build U
        build_undirected!(adjU, outmask, n)
        mU, ΔU, _ = undirected_stats(adjU, n)

        # undirected invariants
        chi  = chromatic_number(adjU, n)
        chip = chromatic_index(adjU, n)
        bip  = is_bipartite(adjU, n) ? 1 : 0
        tri  = triangle_count(adjU, n)
        degen = degeneracy(adjU, n)

        # directed invariants
        scc_c, scc_m = scc_stats(outmask, n)
        ker = has_kernel(outmask, n) ? 1 : 0

        # update hists
        hist_chi[chi] = get(hist_chi, chi, 0) + 1
        hist_chip[chip] = get(hist_chip, chip, 0) + 1
        hist_scc_cnt[scc_c] = get(hist_scc_cnt, scc_c, 0) + 1
        hist_scc_max[scc_m] = get(hist_scc_max, scc_m, 0) + 1
        hist_kernel[ker] = get(hist_kernel, ker, 0) + 1
        hist_mU[mU] = get(hist_mU, mU, 0) + 1
        hist_ΔU[ΔU] = get(hist_ΔU, ΔU, 0) + 1

        # totals for fractions
        cnt_strong += (scc_c == 1 ? 1 : 0)
        cnt_kernel += ker
        cnt_bip    += bip

        # Vizing class
        if chip == ΔU
            vizing_I += 1
            vclass = 1
        elseif chip == ΔU + 1
            vizing_II += 1
            vclass = 2
        else
            vizing_other += 1
            vclass = 9
        end

        # signature
        key = (chi, chip, bip, tri, degen, scc_c, scc_m, ker, min_out, max_out)
        sigcount[key] = get(sigcount, key, 0) + 1

        # optional CSV
        if io !== nothing
            if rowcap == 0 || kept <= rowcap
                @printf(io, "%d,%d,%.6f,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d\n",
                        kept, mdir, dens_dir, ΔD, min_out, max_out,
                        mU, ΔU, chi, chip, vclass, bip, tri, degen, scc_c, scc_m, ker)
            end
        end

        if args.progress > 0 && (checked % args.progress == 0)
            @printf("checked=%d | Piza kept=%d\n", checked, kept)
        end

        if !increment_base3!(digits)
            break
        end
    end

    if io !== nothing
        close(io)
        @printf("\nWrote CSV: %s\n", args.csvfile)
        if rowcap > 0
            @printf("Note: CSV capped at maxrows=%d (kept total=%d)\n", rowcap, kept)
        end
    end

    println("\n==== SUMMARY ====")
    @printf("n=%d | checked=%d | Piza graphs (Δ(D)=0, minout≥%d): %d\n", n, checked, args.minout, kept)

    if kept > 0
        @printf("Fraction strongly connected (SCC count=1): %.6f\n", cnt_strong / kept)
        @printf("Fraction with kernel:                     %.6f\n", cnt_kernel / kept)
        @printf("Fraction bipartite underlying U(D):       %.6f\n", cnt_bip / kept)
    end

    println("\n== Vizing class counts among Piza graphs (underlying U(D)) ==")
    @printf("Class I  (χ' = Δ(U))     : %d\n", vizing_I)
    @printf("Class II (χ' = Δ(U)+1)   : %d\n", vizing_II)
    @printf("Other (sanity check)     : %d\n", vizing_other)

    # Histograms
    print_hist("Histogram of χ(U) over Piza graphs", hist_chi)
    print_hist("Histogram of χ'(U) over Piza graphs", hist_chip)
    print_hist("Histogram of SCC count over Piza graphs", hist_scc_cnt)
    print_hist("Histogram of max SCC size over Piza graphs", hist_scc_max)
    print_hist("Histogram of kernel indicator over Piza graphs (0/1)", hist_kernel)
    print_hist("Histogram of m(U) (# undirected edges) over Piza graphs", hist_mU)
    print_hist("Histogram of Δ(U) (max degree) over Piza graphs", hist_ΔU)

    # Top signatures
    println("\n== Top invariant signatures (most frequent) ==")
    sigs = collect(sigcount)
    sort!(sigs, by = x -> x[2], rev=true)
    limit = min(args.topsig, length(sigs))
    println("count | (chi, chi', bip, tri, degen, scc#, sccmax, kernel, minout, maxout)")
    println("----------------------------------------------------------------------")
    for i in 1:limit
        key, cnt = sigs[i]
        @printf("%5d | %s\n", cnt, string(key))
    end

    println("\nNotes:")
    println("- Counts are for labeled digraphs (no isomorphism reduction).")
    println("- χ'(U) computed exactly via backtracking using Vizing bound (tries Δ(U) and Δ(U)+1).")
    println("- Kernel existence brute-forced over subsets; enumeration limits practical n anyway.")
end

main()
