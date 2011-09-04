#!/usr/bin/env jruby

require "pp"
require "set"

# Hungarian:
# pfm - PF member, a subpattern encoded as an array
# ipfm - PF member index, a integer index referring to a subpattern pfm
# pfc - PF chase member, subpattern in pi projection
# ipfc - PF chase member index, index of subpattern in pi projection
# cms - chase match set
# icms - chase match set index

class Matcher
  def dfs(t, &block)
    yield t
    
    t[1..-1].each do |st|
      dfs(st, &block)
    end
  end

  def add_pattern(pattern)
    @symbol_map ||= {}
    @terminal_map ||= {}
    @arity_map ||= {}

    @patterns ||= []
    @patterns << pattern

    dfs(pattern) do |n|
      sym = n[0]

      @symbol_map[sym] ||= true
      @terminal_map[sym] ||= true if n.size == 1 && n[0] != :*
      @arity_map[sym] = n.size - 1
    end
  end

  def arity_for(sym)
    @arity_map[sym]
  end

  def operators
    @symbol_map.keys.sort { |x, y| x.to_s <=> y.to_s } - terminals - [:*]
  end

  def terminals
    @terminal_map.keys.sort { |x, y| x.to_s <=> y.to_s } - [:*]
  end

  def generate_pf
    @pfm_to_ipfm ||= {}
    @ipfm_to_pfm ||= []

    i_subpat = -1

    @patterns.each do |p|
      dfs(p) do |node|
        @pfm_to_ipfm[node] ||= (i_subpat += 1)
      end
    end

    @pfm_to_ipfm.each do |k, v|
      @ipfm_to_pfm[v] = k
    end
  end

  def generate_pi_proj
    @pi_proj = {}

    operators.each do |op|
      @pi_proj[op] ||= []

      0.upto(arity_for(op) - 1) do |arity|
        ipfc = -1
        @pi_proj[op][arity] = {}

        @pfm_to_ipfm.each do |pfm, ipfm|
          next unless pfm[0] == op
          pfc = pfm[arity + 1]

          if @pfm_to_ipfm[pfc] && !@pi_proj[op][arity][pfc]
            @pi_proj[op][arity][@pfm_to_ipfm[pfc]] = (ipfc += 1) 
          end
        end
      end
    end

    @pi_proj
  end

  # Given array of N arrays, yield arrays of size N which contain every combination of choices
  # from each array
  def all_choices_from(arrs) 
    max_index = arrs.map { |x| x.size }.max - 1

    generate_power_set_of_size((0..max_index).to_a, arrs.size) do |indexes|
      next_set = []

      skip = false

      indexes.each_with_index do |j, i|
        v = arrs[i][j]
        skip ||= v.nil?
        next_set << v
      end

      yield next_set unless skip
    end
  end

  def generate_power_set_of_size(base_set, n, &block)
    stacks = [nil] * n

    step = lambda { |&block|
      stacks.each_with_index do |s, i|
        if s.nil?
          stacks[i] = base_set.dup.to_a
          break
        elsif s.size == 0
          if i > 0
            stacks[i-1].pop
            stacks[i] = nil
          end
        elsif i == n - 1
          yield stacks.map { |s| s.last }
          stacks[i].pop
        end
      end
    }

    loop do
      step.call(&block)
      break if stacks[0].size == 0
    end
  end

  def generate_mu
    @mu = {}
    @theta = {}
    @cms_to_match_set = {}
    @cms_to_icms = {}
    @icms_to_cms = {}

    operators.each do |op|
      @mu[op] ||= []
      @theta[op] ||= {}
      @cms_to_icms[op] ||= []
      @icms_to_cms[op] ||= []

      0.upto(arity_for(op) - 1) do |arity|
        @mu[op][arity] ||= []
        @cms_to_icms[op][arity] ||= {}
        @icms_to_cms[op][arity] ||= []

        icms = -1

        @match_sets.each_with_index do |match_set, i_match_set| 
          cms = Set.new

          match_set.each do |ipfm|
            cms << ipfm if @pi_proj[op][arity][ipfm]
          end

          if cms.size > 0
            cms = cms.to_a.sort
            @cms_to_icms[op][arity][cms] ||= (icms += 1)
            @mu[op][arity][i_match_set] = @cms_to_icms[op][arity][cms]
          end
        end

        @cms_to_icms[op][arity].each do |cms, icms|
          @icms_to_cms[op][arity][icms] = cms
        end
      end

      max_icms_index = @mu[op].map { |x| x.max }.max

      generate_power_set_of_size((0..max_icms_index).to_a, arity_for(op)) do |icms_indexes|
        cmses = []

        skip = false

        icms_indexes.each_with_index do |index, arity|
          cmses[arity] = @icms_to_cms[op][arity][index]
          skip ||= cmses[arity].nil?
          break if skip
        end

        next if skip

        match_set_for_entry = Set.new([@pfm_to_ipfm[[:*]]])

        all_choices_from(cmses) do |cms_choice|
          pfms = cms_choice.map { |ipfm| @ipfm_to_pfm[ipfm] }

          #pfms.each do |pfm|
          #  ipfm = @pfm_to_ipfm[pfm]
          #  match_set_for_entry << ipfm if ipfm
          #end

          ipfm_match = @pfm_to_ipfm[[op] + pfms]
          match_set_for_entry << ipfm_match if ipfm_match
        end

        unless match_set_for_entry.size == 0
          @theta[op][icms_indexes] = @match_sets_to_index[match_set_for_entry.to_a.sort]
        end

      end
    end

    puts @pfm_to_ipfm.inspect
    puts @match_sets.inspect
    puts @match_sets_to_index.inspect
    puts @theta.inspect
    puts @mu.inspect
  end

  def generate_match_sets
    star_ipfm = @pfm_to_ipfm[[:*]]

    @match_sets = [[star_ipfm]]

    terminals.each do |term|
      if @pfm_to_ipfm[[term]]
        @match_sets << [@pfm_to_ipfm[[term]], star_ipfm].sort
      end
    end

    loop do
      next_match_sets = @match_sets.dup
      added_new_match_set = false

      operators.each do |op|
        arity = arity_for(op)

        generate_power_set_of_size((0..@match_sets.size - 1).to_a, arity) do |match_set_choice|
          match_set_candidates = match_set_choice.map { |x| @match_sets[x] }
          # puts "match set candidates: #{match_set_candidates.inspect}"

          new_match_set = [star_ipfm]

          index_span = (0..(match_set_candidates.map { |x| x.size }.max - 1)).to_a

          all_choices_from(match_set_candidates) do |ipfm_choices|
            candidate_pfm = [op]
            bad_pfm = false

            ipfm_choices.each do |ipfm|
              candidate_pfm ||= []
              candidate_pfm << @ipfm_to_pfm[ipfm]
            end

            # puts "candidate_pfm: #{candidate_pfm.inspect}"

            if @pfm_to_ipfm[candidate_pfm]
              # puts "got index #{@pfm_to_ipfm[candidate_pfm]}"
              new_match_set << @pfm_to_ipfm[candidate_pfm]
            end
          end

          # puts "new_match_set: #{new_match_set.inspect}"

          unless next_match_sets.include?(new_match_set.to_a.sort) || new_match_set.size == 0
            next_match_sets << new_match_set.to_a.sort
            added_new_match_set = true
          end
        end
      end

      @match_sets = next_match_sets
      break unless added_new_match_set
    end

    @match_sets_to_index = {}

    @match_sets.each_with_index do |match_set, i|
      @match_sets_to_index[match_set] = i
    end

    @match_sets_to_index
  end
end

m = Matcher.new
m.add_pattern([:a, [:a, [:b], [:*]], [:b]])
m.add_pattern([:a, [:a, [:*], [:c]], [:c]])
m.generate_pf
m.generate_pi_proj
m.generate_match_sets
m.generate_mu
