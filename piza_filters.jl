#!/usr/bin/env julia
# =============================================================================
# piza_filters.jl
#
# Enumerate Piza graphs (Δ(D)=0) on n vertices (n<=6 recommended), with minout>=k,
# compute invariants, and produce:
#   - global histograms/counters for all Piza graphs
#   - conditional histograms/counters for:
#       (A) strongly connected Piza graphs (SCC count = 1)
#       (B) Vizing Class II Piza graphs (χ'(U)=Δ(U)+1)
#       (C) intersection (A) ∩ (B)
# Optional CSV outputs for each subset.
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
# Underlying undirected graph U(D)
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
    color = fill(0, n)
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

function chromatic_index(adjU::Vector{UInt64}, n::Int)
    edges = undirected_edges(adjU, n)
    m = length(edges)
    if m == 0
        return 0
    end
    ΔU = 0
    for v in 1:n
        ΔU = max(ΔU, popcount64(adjU[v]))
    end

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
# SCC (Kosaraju)
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
# Kernel existence (bruteforce subsets)
# ----------------------------
function has_kernel(outmask::Vector{UInt64}, n::Int)
    for S in 0:(UInt64(1)<<n)-1
        if S == 0
            continue
        end

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
# histogram helpers
# ----------------------------
function add_hist!(hist::Dict{Int,Int}, k::Int)
    hist[k] = get(hist, k, 0) + 1
end

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
    csv_all = ""
    csv_sc  = ""
    csv_v2  = ""
    csv_sc_v2 = ""
    maxrows = 0

    i = 1
    while i <= length(ARGS)
        arg = ARGS[i]
        if arg == "--minout"
            minout = parse(Int, ARGS[i+1]); i += 2
        elseif arg == "--progress"
            progress = parse(Int, ARGS[i+1]); i += 2
        elseif arg == "--csv_all"
            csv_all = ARGS[i+1]; i += 2
        elseif arg == "--csv_sc"
            csv_sc = ARGS[i+1]; i += 2
        elseif arg == "--csv_v2"
            csv_v2 = ARGS[i+1]; i += 2
        elseif arg == "--csv_sc_v2"
            csv_sc_v2 = ARGS[i+1]; i += 2
        elseif arg == "--maxrows"
            maxrows = parse(Int, ARGS[i+1]); i += 2
        else
            if n === nothing
                n = parse(Int, arg); i += 1
            else
                error("Unrecognized argument: $arg")
            end
        end
    end
    n === nothing && error("Usage: julia piza_filters.jl 6 [--minout 1] [--csv_sc sc.csv] ...")
    return (n=n, minout=minout, progress=progress,
            csv_all=csv_all, csv_sc=csv_sc, csv_v2=csv_v2, csv_sc_v2=csv_sc_v2,
            maxrows=maxrows)
end

function open_csv(path::String)
    if isempty(path)
        return nothing
    end
    io = open(path, "w")
    println(io, "id,edges_dir,density_dir,min_out,max_out,mU,DeltaU,chi,chi_index,vizing_class,bipartite,triangles,degeneracy,scc_count,scc_max,kernel")
    return io
end

# ----------------------------
# Main
# ----------------------------
function main()
    args = parse_args()
    n = args.n
    n > 63 && error("Requires n <= 63.")
    pairs = pairs_list(n)
    m = length(pairs)
    @printf("n=%d, pairs=%d, total oriented graphs = 3^%d = %s\n", n, m, m, string(big(3)^big(m)))
    @printf("Filtering: Piza graphs = Δ(D)=0 and min outdegree >= %d\n", args.minout)

    digits  = fill(UInt8(0), m)
    outmask = fill(UInt64(0), n)
    adjU    = fill(UInt64(0), n)

    # CSVs
    io_all = open_csv(args.csv_all)
    io_sc  = open_csv(args.csv_sc)
    io_v2  = open_csv(args.csv_v2)
    io_sc_v2 = open_csv(args.csv_sc_v2)
    cap = args.maxrows

    # Counters
    checked = 0
    kept_all = 0
    kept_sc = 0
    kept_v2 = 0
    kept_sc_v2 = 0

    # Fractions for ALL
    cnt_all_kernel = 0
    cnt_all_bip = 0
    cnt_all_strong = 0
    vizing_I_all = 0
    vizing_II_all = 0

    # Histograms for ALL and subsets
    function init_bundle()
        return (
            chi = Dict{Int,Int}(),
            chip = Dict{Int,Int}(),
            scc_cnt = Dict{Int,Int}(),
            scc_max = Dict{Int,Int}(),
            kernel = Dict{Int,Int}(),
            mU = Dict{Int,Int}(),
            ΔU = Dict{Int,Int}(),
        )
    end
    H_all = init_bundle()
    H_sc  = init_bundle()
    H_v2  = init_bundle()
    H_sc_v2 = init_bundle()

    function upd!(H, chi, chip, scc_c, scc_m, ker, mU, ΔU)
        add_hist!(H.chi, chi)
        add_hist!(H.chip, chip)
        add_hist!(H.scc_cnt, scc_c)
        add_hist!(H.scc_max, scc_m)
        add_hist!(H.kernel, ker)
        add_hist!(H.mU, mU)
        add_hist!(H.ΔU, ΔU)
    end

    function write_row(io, id, mdir, dens_dir, min_out, max_out, mU, ΔU, chi, chip, vclass, bip, tri, degen, scc_c, scc_m, ker)
        io === nothing && return
        # Fast, no format-specifier mismatch possible:
        println(io,
            id, ",",
            mdir, ",",
            @sprintf("%.6f", dens_dir), ",",
            min_out, ",",
            max_out, ",",
            mU, ",",
            ΔU, ",",
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

    while true
        checked += 1
        build_outmask!(outmask, digits, pairs)

        min_out, max_out, mdir = outdeg_stats(outmask, n)
        if min_out < args.minout
            if !increment_base3!(digits); break; end
            continue
        end

        if delta_D(outmask, n) != 0
            if !increment_base3!(digits); break; end
            continue
        end

        # Piza graph
        kept_all += 1
        dens_dir = mdir / (n*(n-1))

        build_undirected!(adjU, outmask, n)
        mU, ΔU, _ = undirected_stats(adjU, n)

        chi = chromatic_number(adjU, n)
        chip = chromatic_index(adjU, n)
        bip = is_bipartite(adjU, n) ? 1 : 0
        tri = triangle_count(adjU, n)
        degen = degeneracy(adjU, n)
        scc_c, scc_m = scc_stats(outmask, n)
        ker = has_kernel(outmask, n) ? 1 : 0

        vclass = 9
        if chip == ΔU
            vclass = 1
            vizing_I_all += 1
        elseif chip == ΔU + 1
            vclass = 2
            vizing_II_all += 1
        end

        cnt_all_kernel += ker
        cnt_all_bip += bip
        cnt_all_strong += (scc_c == 1 ? 1 : 0)

        upd!(H_all, chi, chip, scc_c, scc_m, ker, mU, ΔU)

        # subsets
        is_sc = (scc_c == 1)
        is_v2 = (vclass == 2)
        is_sc_v2 = is_sc && is_v2

        if is_sc
            kept_sc += 1
            upd!(H_sc, chi, chip, scc_c, scc_m, ker, mU, ΔU)
        end
        if is_v2
            kept_v2 += 1
            upd!(H_v2, chi, chip, scc_c, scc_m, ker, mU, ΔU)
        end
        if is_sc_v2
            kept_sc_v2 += 1
            upd!(H_sc_v2, chi, chip, scc_c, scc_m, ker, mU, ΔU)
        end

        # CSV output with caps per subset (cap applies to each output separately)
        if io_all !== nothing && (cap == 0 || kept_all <= cap)
            write_row(io_all, kept_all, mdir, dens_dir, min_out, max_out, mU, ΔU, chi, chip, vclass, bip, tri, degen, scc_c, scc_m, ker)
        end
        if io_sc !== nothing && is_sc && (cap == 0 || kept_sc <= cap)
            write_row(io_sc, kept_sc, mdir, dens_dir, min_out, max_out, mU, ΔU, chi, chip, vclass, bip, tri, degen, scc_c, scc_m, ker)
        end
        if io_v2 !== nothing && is_v2 && (cap == 0 || kept_v2 <= cap)
            write_row(io_v2, kept_v2, mdir, dens_dir, min_out, max_out, mU, ΔU, chi, chip, vclass, bip, tri, degen, scc_c, scc_m, ker)
        end
        if io_sc_v2 !== nothing && is_sc_v2 && (cap == 0 || kept_sc_v2 <= cap)
            write_row(io_sc_v2, kept_sc_v2, mdir, dens_dir, min_out, max_out, mU, ΔU, chi, chip, vclass, bip, tri, degen, scc_c, scc_m, ker)
        end

        if args.progress > 0 && (checked % args.progress == 0)
            @printf("checked=%d | Piza=%d | SC=%d | V2=%d | SC∩V2=%d\n",
                    checked, kept_all, kept_sc, kept_v2, kept_sc_v2)
        end

        if !increment_base3!(digits)
            break
        end
    end

    for io in (io_all, io_sc, io_v2, io_sc_v2)
        if io !== nothing
            close(io)
        end
    end

    println("\n==== SUMMARY (ALL Piza) ====")
    @printf("n=%d | checked=%d | Piza (Δ=0, minout≥%d): %d\n", n, checked, args.minout, kept_all)
    if kept_all > 0
        @printf("Strongly connected fraction: %.6f\n", cnt_all_strong / kept_all)
        @printf("Kernel fraction:            %.6f\n", cnt_all_kernel / kept_all)
        @printf("Bipartite(U) fraction:      %.6f\n", cnt_all_bip / kept_all)
    end
    println("\nVizing class among ALL Piza (U):")
    @printf("Class I : %d\n", vizing_I_all)
    @printf("Class II: %d\n", vizing_II_all)

    println("\n==== SUBSET SIZES ====")
    @printf("Strongly connected Piza: %d\n", kept_sc)
    @printf("Vizing Class II Piza:    %d\n", kept_v2)
    @printf("Intersection SC ∩ V2:    %d\n", kept_sc_v2)

    # Print subset histograms (lightweight but informative)
    println("\n---- Histograms (ALL Piza) ----")
    print_hist("χ(U)", H_all.chi)
    print_hist("χ'(U)", H_all.chip)
    print_hist("SCC count", H_all.scc_cnt)
    print_hist("max SCC size", H_all.scc_max)
    print_hist("kernel (0/1)", H_all.kernel)
    print_hist("m(U)", H_all.mU)
    print_hist("Δ(U)", H_all.ΔU)

    println("\n---- Histograms (Strongly connected Piza) ----")
    print_hist("χ(U)", H_sc.chi)
    print_hist("χ'(U)", H_sc.chip)
    print_hist("kernel (0/1)", H_sc.kernel)
    print_hist("m(U)", H_sc.mU)
    print_hist("Δ(U)", H_sc.ΔU)

    println("\n---- Histograms (Vizing Class II Piza) ----")
    print_hist("χ(U)", H_v2.chi)
    print_hist("χ'(U)", H_v2.chip)
    print_hist("SCC count", H_v2.scc_cnt)
    print_hist("max SCC size", H_v2.scc_max)
    print_hist("kernel (0/1)", H_v2.kernel)
    print_hist("m(U)", H_v2.mU)
    print_hist("Δ(U)", H_v2.ΔU)

    println("\n---- Histograms (SC ∩ Vizing II) ----")
    print_hist("χ(U)", H_sc_v2.chi)
    print_hist("χ'(U)", H_sc_v2.chip)
    print_hist("kernel (0/1)", H_sc_v2.kernel)
    print_hist("m(U)", H_sc_v2.mU)
    print_hist("Δ(U)", H_sc_v2.ΔU)
end

main()
