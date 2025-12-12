# Copyright 2025 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# ==============================================================================

"""The logic core of AlphaGeometry2."""

import collections
import fractions
import itertools

import elimination as el
import numericals as ng
from parse import AGPoint


Fraction = fractions.Fraction
DefaultDict = collections.defaultdict
NumCircle = ng.NumCircle
NumLine = ng.NumLine

# Added ProofNode class to track proof steps
class ProofNode:
  def __init__(self, rule_name, statement, parents=None):
    self.rule_name = rule_name
    self.statement = statement 
    self.parents = parents if parents else []
    self.id = id(self)

  def __repr__(self):
    return f"ProofNode({self.rule_name}: {self.statement})"

  def __hash__(self):
    return self.id

  def __eq__(self, other):
    return self.id == other.id

class FormalLine:
  """Points known to be collinear (immutable)."""

  def __init__(
      self,
      points: list[AGPoint],
      main_pair: tuple[AGPoint, AGPoint],
      direction: el.FormalAngle,
      value: NumLine,
      sources: set[ProofNode] | None = None
  ):
    assert len(points) > 1
    self.points = points
    self.main_pair = main_pair
    self.direction = direction
    self.value = value
    self.sources = sources if sources else set()


class FormalCircle:
  """Points known to be concyclic, possibly with a center (immutable)."""

  def __init__(
      self,
      defining_points: list[AGPoint],
      points: list[AGPoint],
      centers: list[AGPoint],
      value: NumCircle,
      sources: set[ProofNode] | None = None
  ):
    self.defining_points = defining_points
    self.points = points
    self.centers = centers
    self.value = value
    self.sources = sources if sources else set()


class DDAR:
  """Main logical engine."""

  def __init__(self, points):

    self.points = list(points)
    assert all(isinstance(point, AGPoint) for point in points)
    self.lines = set()
    self.circles = set()
    
    self.proof_steps = []

    self.elim_dist_mul = el.ElimDistMul()
    self.elim_dist_add = el.ElimDistAdd()
    self.elim_angle = el.ElimAngle()

    self.point_subst = {x: x for x in points}
    self.pair_to_line = dict()

    self.pair_to_dist_mul = dict()
    self.pair_to_dist_add = dict()
    self.pair_to_dir = dict()

    for a, b in itertools.combinations(self.points, 2):

      if ng.distance(a.value, b.value) < ng.ATOM:
        continue

      num_line = NumLine.through(a.value, b.value)
      num_direction = num_line.direction()
      direction = self.elim_angle.new_var(num_direction, f'd({a} {b})')
      
      # Initial trivial lines have no proof cause (axioms)
      line = FormalLine(
          points=[a, b],
          main_pair=(a, b),
          direction=direction,
          value=num_line,
          sources=set() 
      )
      self.pair_to_dir[a, b] = direction
      self.pair_to_dir[b, a] = direction
      self.pair_to_line[a, b] = line
      self.pair_to_line[b, a] = line
      self.lines.add(line)

      dist = ng.distance(a.value, b.value)

      dist_mul = self.elim_dist_mul.new_var(dist, f'log(|{a} {b}|)')
      self.pair_to_dist_mul[a, b] = dist_mul
      self.pair_to_dist_mul[b, a] = dist_mul

      dist_add = self.elim_dist_add.new_var(dist, f'|{a} {b}|')
      self.pair_to_dist_add[a, b] = dist_add
      self.pair_to_dist_add[b, a] = dist_add

    self.known_similar = set()
    self.triple_to_circle = dict() 
    self.last_small_circles = []  
    self.dist_mul_cache = dict(self.pair_to_dist_mul)
    self.direction_cache = dict(self.pair_to_dir)

  def num_identical(self, a, b):
    return (a, b) not in self.pair_to_dist_mul

  # Added proof tracking to force_pred and related methods
  def force_pred(self, pred):
    """Adds a predicate as an assumption."""
    pred_orig = pred 
    pred = pred.replace_points(self.point_subst)
    
    cause = ProofNode("Given", str(pred_orig))
    self.proof_steps.append(cause)

    if pred.name == 'coll':
      self.force_collinear(pred.points, cause=cause)
    elif pred.name in ('angeq', 'para', 'perp', 's_angle', 'aconst', 'eqangle'):
      self.elim_angle.force_zero(self.pred_to_angle(pred), cause=cause)
    elif pred.name in ('distmeq', 'cong', 'eqratio', 'rconst'):
      self.elim_dist_mul.force_one(self.pred_to_dist_mul(pred), cause=cause)
    elif pred.name == 'distseq':
      self.elim_dist_add.force_zero(self.pred_to_dist_add(pred), cause=cause)
    elif pred.name == 'cyclic':
      self.force_concyclic(pred.points, (), cause=cause)
    elif pred.name == 'cyclic_with_centers':
      [num_centers] = pred.constants
      centers = pred.points[:num_centers]
      points = pred.points[num_centers:]
      distinct_points = []
      for x in points:
        if not any(self.num_identical(x, y) for y in distinct_points):
          distinct_points.append(x)
          if len(distinct_points) == 3:
            break
      if len(distinct_points) >= 3:
        self.force_concyclic(points, centers, cause=cause)
      else:
        a0 = points[0]
        c0 = centers[0]
        d0 = self.get_dist_mul(a0, c0)
        for a in points:
          for c in centers:
            d = self.get_dist_mul(a, c)
            self.elim_dist_mul.force_one(d0 / d, cause=cause)
    elif pred.name == 'overlap':
      a, b = pred.points
      self.force_equal_points(a, b, cause=cause)
    elif pred.name == 'acompute':
      print("Warning: acompute predicate doesn't make sense to be forced")
      return
    else:
      raise ValueError('Unexpected predicate:', pred.name)

  def pred_to_angle(self, pred):
    """Translate an angle predicate into an equation."""
    if pred.name == 'angeq':
      assert len(pred.points) == 2 * (len(pred.constants) - 1)
      coefs = pred.constants[:-1]
      const = pred.constants[-1]
      comb = el.LinComb.zero()
      for i, coef in enumerate(coefs):
        a, b = pred.points[2 * i : 2 * (i + 1)]
        comb.iadd_mul(self.pair_to_dir[a, b].comb, coef)
      comb += self.elim_angle.const_frac(Fraction(const) / 180).comb
      return el.FormalAngle(comb)
    elif pred.name == 'eqangle':
      a1, a2, b1, b2, c1, c2, d1, d2 = pred.points
      ang1 = self.pair_to_dir[a1, a2] - self.pair_to_dir[b1, b2]
      ang2 = self.pair_to_dir[c1, c2] - self.pair_to_dir[d1, d2]
      return ang1 - ang2
    elif pred.name == 'para':
      a1, a2, b1, b2 = pred.points
      ang = self.pair_to_dir[a1, a2] - self.pair_to_dir[b1, b2]
      return ang
    elif pred.name == 'perp':
      a1, a2, b1, b2 = pred.points
      ang = (
          self.pair_to_dir[a1, a2]
          - self.pair_to_dir[b1, b2]
          - self.elim_angle.const(1, 2)
      )
      return ang
    elif pred.name in ['s_angle', 'aconst']:
      a1, a2, b1, b2 = pred.points
      [ang] = pred.constants
      ang = Fraction(ang) / Fraction(180)
      ang0 = (
          self.pair_to_dir[a1, a2]
          - self.pair_to_dir[b1, b2]
          - self.elim_angle.const_frac(ang)
      )
      return ang0
    else:
      raise ValueError('Not an angle predicate:', pred.name)

  def pred_to_dist_mul(self, pred):
    """Translate a multiplicative-distance predicate into a log-equation."""
    if pred.name == 'distmeq':
      assert len(pred.points) == 2 * (len(pred.constants) - 1)
      coefs = pred.constants[:-1]
      const = pred.constants[-1]
      assert const > 0
      comb = el.LinComb.zero()
      for i, coef in enumerate(coefs):
        a, b = pred.points[2 * i : 2 * (i + 1)]
        comb.iadd_mul(self.pair_to_dist_mul[a, b].comb, coef)
      return el.DistMul(comb) * const
    elif pred.name == 'cong':
      a, b, c, d = pred.points
      d1 = self.get_dist_mul(a, b)
      d2 = self.get_dist_mul(c, d)
      return d1 / d2
    elif pred.name == 'rconst':
      a, b, c, d = pred.points
      d1 = self.get_dist_mul(a, b)
      d2 = self.get_dist_mul(c, d)
      [const] = pred.constants
      return d1 / d2 / Fraction(const)
    elif pred.name == 'eqratio':
      a, b, c, d, e, f, g, h = pred.points
      rat1 = self.get_dist_ratio(a, b, c, d)
      rat2 = self.get_dist_ratio(e, f, g, h)
      return rat1 / rat2
    else:
      raise ValueError('Not a ratio predicate:', pred.name)

  def pred_to_dist_add(self, pred):
    if pred.name == 'distseq':
      assert len(pred.points) == 2 * len(pred.constants)
      _ = pred.constants[:-1]
      comb = el.LinComb.zero()
      for i, coef in enumerate(pred.constants):
        a, b = pred.points[2 * i : 2 * (i + 1)]
        comb.iadd_mul(self.pair_to_dist_add[a, b].comb, coef)
      return el.DistAdd(comb)
    else:
      raise ValueError('Not a sum predicate:', pred.name)

  def check_pred(self, pred):
    """Returns whether a predicate is known to be satisfied (in the DB)."""

    if pred.name != 'overlap':
      pred = pred.replace_points(self.point_subst)

    if pred.name == 'coll':
      return self.check_collinear(pred.points)
    elif pred.name in ('angeq', 'para', 'perp', 's_angle', 'aconst', 'eqangle'):
      res = self.pred_to_angle(pred)
      res = self.elim_angle.simplify(res)
      return res.is_zero()
    elif pred.name in ('distmeq', 'cong', 'eqratio', 'rconst'):
      res = self.pred_to_dist_mul(pred)
      res = self.elim_dist_mul.simplify(res)
      return res.is_one()
    elif pred.name == 'distseq':
      res = self.pred_to_dist_add(pred)
      res = self.elim_dist_add.simplify(res)
      return res.is_zero()
    elif pred.name == 'cyclic':
      return self.check_concyclic(pred.points)
    elif pred.name == 'cyclic_with_centers':
      [num_centers] = pred.constants
      centers = pred.points[:num_centers]
      points = pred.points[num_centers:]
      return self.check_concyclic(points, centers)
    elif pred.name == 'overlap':
      a, b = pred.points
      return self.check_equal_points(a, b)
    elif pred.name == 'acompute':
      a1, a2, b1, b2 = pred.points
      ang = self.pair_to_dir[a1, a2] - self.pair_to_dir[b1, b2]
      ang = self.elim_angle.simplify(ang)
      if all(v == el.angle_unit for v in ang.comb.d.keys()):
        return ang.comb.d.get(el.angle_unit, Fraction(0))
      else:
        return None
    else:
      raise ValueError('Unexpected predicate:', pred.name)
  
  def get_proof(self, pred):
    """Generates and prints the proof trace for the given predicate."""
    print(f"\n[Proof Trace for: {pred}]")
    
    parents = set()
    goal_node = None
    
    if pred.name != 'overlap':
      pred = pred.replace_points(self.point_subst)

    # Handle 'coll' and 'cyclic' by looking up source in FormalLine/Circle
    if pred.name == 'coll':
        # Retrieve the line that contains these points
        # Assuming check_collinear has already passed
        points = pred.points
        if len(points) >= 2:
            line = self.pair_to_line.get((points[0], points[1]))
            if line:
                parents = line.sources
    elif pred.name == 'cyclic' or pred.name == 'cyclic_with_centers':
      # Retrieve the circle
      # Use first 3 distinct points to find the FormalCircle key
      points = pred.points
      if pred.name == 'cyclic_with_centers':
        [num_centers] = pred.constants
        points = points[num_centers:]
      
      distinct_points = []
      for point in points:
        if any(self.num_identical(point, x) for x in distinct_points): continue
        distinct_points.append(point)
      
      if len(distinct_points) >= 3:
        circle = self.triple_to_circle.get(tuple(distinct_points[:3]))
        if circle:
            parents = circle.sources
    elif pred.name == 'acompute':
      a1, a2, b1, b2 = pred.points
      ang = self.pair_to_dir[a1, a2] - self.pair_to_dir[b1, b2]
      ang = self.elim_angle.simplify(ang)
      parents = ang.comb.sources
      
      val_frac = ang.comb.d.get(el.angle_unit, Fraction(0))
      val_degrees = float(val_frac * 180)
      
      goal_node = ProofNode(
          "Computation", 
          f"{pred} = {val_degrees:.2f}°", 
          parents=list(parents)
      )
    elif pred.name in ('angeq', 'para', 'perp', 's_angle', 'aconst', 'eqangle'):
      res = self.pred_to_angle(pred)
      res = self.elim_angle.simplify(res)
      parents = res.comb.sources
    elif pred.name in ('distmeq', 'cong', 'eqratio', 'rconst'):
      res = self.pred_to_dist_mul(pred)
      res = self.elim_dist_mul.simplify(res)
      parents = res.comb.sources
    elif pred.name == 'distseq':
      res = self.pred_to_dist_add(pred)
      res = self.elim_dist_add.simplify(res)
      parents = res.comb.sources
      
    # BFS/Topological sort to print the trace
    visited = set()
    queue = list(sorted(parents, key=lambda n: n.id))
    
    all_nodes = []
    def collect(node):
      if node.id in visited: return
      visited.add(node.id)
      for p in node.parents:
        collect(p)
      all_nodes.append(node)

    for p in queue:
      collect(p)

    if goal_node:
      all_nodes.append(goal_node)

    if not all_nodes:
      print("  (No proof trace available - premise or axiom?)")

    for i, node in enumerate(all_nodes):
      parents_idx = []
      for p in node.parents:
        try:
          parents_idx.append(str(all_nodes.index(p)))
        except ValueError:
          pass 
      
      p_str = f" [Parents: {', '.join(parents_idx)}]" if parents_idx else ""
      print(f"Step {i}: {node.statement} (Rule: {node.rule_name}){p_str}")

  ####### Loop
  def deduction_closure(self, verbose=False, progress_dot=True):
    """Infers all further facts deducible on the given point."""
    # self.elim_dist_mul.core.display()
    changed = True
    while changed:
      # for _ in range(5):
      if not verbose and progress_dot:
        print('.', flush=True, end='')
      self.update_cache()
      changed = False

      if verbose:
        print('  Similar triangles...')
      changed_last = self.search_similar(verbose=verbose)
      changed = changed or changed_last
      if changed_last:
        self.update_cache()
      if verbose:
        print('  ... similar triangles      ', end='')
        print(['----', 'Updated'][changed_last])

      if verbose:
        print('  Cyclic quadrilaterals...   ', end='')
      changed_last = self.search_concyclic()
      changed = changed or changed_last
      if changed_last:
        self.update_cache()
      if verbose:
        print(['----', 'Updated'][changed_last])

      if verbose:
        print('  Circles...                 ', end='')
      changed_last = self.search_circles()
      changed = changed or changed_last
      if verbose:
        print(['----', 'Updated'][changed_last])

      if verbose:
        print('  Merging points...          ', end='')
      changed_last = self.merge_points()
      changed = changed or changed_last
      if verbose:
        print(['----', 'Updated'][changed_last])

      if verbose:
        print('  Sync add / mul dist...     ', end='')
      changed_last = self.transfer_dist_add_mul()
      changed = changed or changed_last
      if verbose:
        print(['----', 'Updated'][changed_last])

      if verbose:
        print('  Sync segments / arcs...    ', end='')
      changed_last = self.transfer_dist_arc_mul()
      changed = changed or changed_last
      if verbose:
        print(['----', 'Updated'][changed_last])

  def search_similar(self, verbose):
    """Looks for similar triangles, and infers approproate facts."""
    sss = dict()
    aa = dict()
    sas = dict()
    ssa = dict()
    ssa_triangles = set()
    similar_pairs = []
    count = 0
    for a in self.points:
      for b in self.points:
        if self.num_identical(a, b):
          continue
        encountered = self.elim_angle.was_encountered(
            self.pair_to_dir[a, b]
        ) or self.elim_dist_mul.was_encountered(self.pair_to_dist_mul[a, b])
        if not encountered:
          continue
        for c in self.points:
          if self.num_identical(a, c):
            continue
          if self.num_identical(b, c):
            continue
          orient = ng.orientation(a.value, b.value, c.value)
          if orient == 0:
            continue
          count += 1
          
          rat1_obj = self.get_dist_ratio(a, b, a, c)
          ang1_obj = self.get_point_angle(a, b, a, c)
          rat2_obj = self.get_dist_ratio(c, b, c, a)
          ang2_obj = self.get_point_angle(c, b, c, a)
          
          rat1 = rat1_obj 
          rat2 = rat2_obj
          ang1 = ang1_obj
          ang2 = ang2_obj

          if (rat1, rat2) in sss:
            (a0, b0, c0), (r1_src, r2_src) = sss[rat1, rat2]
            deps = rat1_obj.comb.sources | rat2_obj.comb.sources | r1_src.comb.sources | r2_src.comb.sources
            similar_pairs.append(((a0, b0, c0), (a, b, c), "SSS", deps))
          else:
            sss[rat1, rat2] = (a, b, c), (rat1_obj, rat2_obj)

          if (ang1, ang2) in aa:
            (a0, b0, c0), (a1_src, a2_src) = aa[ang1, ang2]
            deps = ang1_obj.comb.sources | ang2_obj.comb.sources | a1_src.comb.sources | a2_src.comb.sources
            similar_pairs.append(((a0, b0, c0), (a, b, c), "AA", deps))
          else:
            aa[ang1, ang2] = (a, b, c), (ang1_obj, ang2_obj)
            aa[-ang1, -ang2] = (a, b, c), (-ang1_obj, -ang2_obj) 

          if (ang1, rat1, orient) in sas:
            (a0, b0, c0), (a1_src, r1_src) = sas[ang1, rat1, orient]
            deps = ang1_obj.comb.sources | rat1_obj.comb.sources | a1_src.comb.sources | r1_src.comb.sources
            similar_pairs.append(((a0, b0, c0), (a, b, c), "SAS", deps))
          else:
            sas[ang1, rat1, orient] = (a, b, c), (ang1_obj, rat1_obj)
            sas[-ang1, rat1, -orient] = (a, b, c), (-ang1_obj, rat1_obj)

          for a1, b1, c1, ang, rat, cur_orient, ang_obj in (
              (a, b, c, ang1, rat2, orient, ang1_obj),
              (c, b, a, ang2, rat1, -orient, ang2_obj),
          ):
            if (
                ng.distance(c1.value, b1.value)
                - ng.distance(c1.value, a1.value)
                > ng.ATOM
            ):
              if (a1, b1, c1) in ssa_triangles:
                continue
              ssa_triangles.add((a1, b1, c1))
              
              rat_obj = rat2_obj if rat is rat2 else rat1_obj
              
              if (ang, rat, cur_orient) in ssa:
                (a0, b0, c0), (a0_src, r0_src) = ssa[ang, rat, cur_orient]
                deps = ang_obj.comb.sources | rat_obj.comb.sources | a0_src.comb.sources | r0_src.comb.sources
                similar_pairs.append(((a0, b0, c0), (a1, b1, c1), "SSA", deps))
              else:
                ssa[ang, rat, cur_orient] = (a1, b1, c1), (ang_obj, rat_obj)
                ssa[-ang, rat, -cur_orient] = (a1, b1, c1), (-ang_obj, rat_obj)

    if verbose:
      print(f'    {count} triangles checked')
      print(f'    {len(similar_pairs)} similar pairs found')

    changed = False
    for triangle1, triangle2, rule, deps in similar_pairs:
      tn1 = "".join([p.name for p in triangle1])
      tn2 = "".join([p.name for p in triangle2])
      stmt = f"sim {tn1} {tn2}"
      node = ProofNode(rule, stmt, parents=list(deps))
      self.proof_steps.append(node)
      
      changed = self.force_similar(triangle1, triangle2, cause=node) or changed

    return changed

  def search_concyclic(self):
    """Looks for cyclic quadrilaterals, and infers appropriate facts."""
    changed = False
    for a in self.points:
      for b in self.points:
        ang_to_points_centers = DefaultDict(lambda: ([], [], set())) 
        on_line = []
        on_line_sources = set()
        
        for c in self.points:
          if self.num_identical(a, c):
            continue
          if self.num_identical(b, c):
            continue

          # 'c' on the circle
          ang_obj = self.get_point_angle(c, a, c, b)
          ang = ang_obj

          if ang.is_zero():
            on_line.append(c)
            on_line_sources.update(ang_obj.comb.sources)

          if self.num_identical(a, b):
            continue

          if not ng.collinear(a.value, b.value, c.value):
            points, _, src = ang_to_points_centers[ang]
            points.append(c)
            src.update(ang_obj.comb.sources)

          dist_ratio_obj = self.get_dist_ratio(c, a, c, b)
          dist_ratio = dist_ratio_obj
          
          if dist_ratio.is_one():  # 'c' as a center
            halfang_obj = self.get_point_angle(a, c, a, b) + self.elim_angle.const(
                1, 2
            )
            halfang = halfang_obj
            
            _, centers, src = ang_to_points_centers[halfang]
            centers.append(c)
            src.update(dist_ratio_obj.comb.sources)
            src.update(halfang_obj.comb.sources)

        for c in on_line:
           stmt = f"coll {a} {b} {c}"
           node = ProofNode("AngleZero", stmt, parents=list(on_line_sources))
           self.proof_steps.append(node)
           changed = self.force_collinear([a, b, c], cause=node) or changed

        for points, centers, sources in ang_to_points_centers.values():
          if len(points) >= 2 or (centers and points):
            all_pts = [a, b] + points
            pt_names = " ".join([p.name for p in all_pts])
            stmt = f"cyclic {pt_names}"
            node = ProofNode("ConcyclicAngles", stmt, parents=list(sources))
            self.proof_steps.append(node)
            changed = self.force_concyclic(all_pts, centers, cause=node) or changed

    return changed

  def search_circles(self):
    """Looks for equal distances implying a circle."""
    changed = False
    self.last_small_circles = []

    for a in self.points:
      dist_to_points = dict()
      for b in self.points:
        if self.num_identical(a, b):
          continue
        dist_obj = self.get_dist_mul(a, b)
        dist = dist_obj
        if dist not in dist_to_points:
          dist_to_points[dist] = [(b, dist_obj)]
        else:
          dist_to_points[dist].append((b, dist_obj))

      for _, points_data in dist_to_points.items():
        if len(points_data) <= 1:
          continue
        
        all_sources = set()
        for _, dobj in points_data:
            all_sources.update(dobj.comb.sources)

        distinct_points = []
        for point, _ in points_data:
          if any(self.num_identical(point, x) for x in distinct_points):
            continue
          distinct_points.append(point)
        points_only = [point for point, _ in points_data]

        if len(distinct_points) >= 3:
          pt_names = " ".join([p.name for p in points_only])
          stmt = f"cyclic {pt_names} center {a.name}"
          node = ProofNode("EqualDistances", stmt, parents=list(all_sources))
          self.proof_steps.append(node)
          changed = self.force_concyclic(points_only, (a,), cause=node) or changed
        else:
          # Small circles don't really have proofs until they merge
          self.last_small_circles.append(
              FormalCircle(
                  defining_points=None,
                  points=points_only,
                  centers=(a,),
                  value=NumCircle(
                      center=a.value,
                      r=ng.distance(a.value, points_only[0].value),
                  ),
                  sources=set()
              )
          )

    return changed

  def merge_points(self):
    """Looks for points that are provably equal, and merges them."""

    changed = False
    # find objects passing through pairs of equal points
    same_pairs = {
        (a, b): []
        for a, b in itertools.combinations(self.points, 2)
        if self.num_identical(a, b)
    }
    if not same_pairs:
      return False

    for obj in itertools.chain(
        self.lines, self.last_small_circles, self.circles
    ):
      for a in obj.points:
        for b in obj.points:
          l = same_pairs.get((a, b))
          if l is None:
            continue
          l.append(obj)

    # merge multiple centers of the same circle
    for circle in list(self.circles):
      if len(circle.centers) > 1:
        for center in circle.centers[1:]:
          # Cause? Implicit from circle definition
          self.force_equal_points(circle.centers[0], center, cause=None)

    # if two such objects for a single pair are not tangent, merge them
    for (a, b), objs in same_pairs.items():
      if len(objs) <= 1:
        continue
      intersection_dirs = []
      for obj in objs:
        if isinstance(obj, FormalCircle):
          intersection_dirs.append(
              ng.direction(a.value - obj.value.center) + 0.5
          )
        elif isinstance(obj, FormalLine):
          intersection_dirs.append(obj.value.direction())
        else:
          raise ValueError(f'Unexpected type {type(obj)}')
      d0 = intersection_dirs[0]
      for d1 in intersection_dirs[1:]:
        if abs((d0 - d1 + 0.5) % 1 - 0.5) ** 2 >= ng.ATOM:
          # Merge caused by intersection
          # Ideally we would grab sources from 'objs' here
          sources = set()
          for obj in objs:
              if hasattr(obj, 'sources'):
                  sources.update(obj.sources)
          
          cause = ProofNode("IntersectionMerge", f"overlap {a} {b}", parents=list(sources))
          self.proof_steps.append(cause)
          self.force_equal_points(a, b, cause=cause) 
          changed = (
              True  
          )
          break

    if changed:
      self.update_cache()
    return changed

  def transfer_dist_add_mul(self):
    """Translate the facts between additive / multiplicative distance groups."""
    changed = False
    mul_to_add = dict()
    add_to_mul = dict()
    for a, b in itertools.combinations(self.points, 2):
      if self.num_identical(a, b):
        continue
      mul_obj = self.get_dist_mul(a, b)
      add_obj = self.get_dist_add(a, b)
      
      mul = mul_obj
      add = add_obj
      
      mul_n, mul_coef = mul.normalize()
      add_n, add_coef = add.normalize()
      
      mul1 = mul / add_coef 
      add1 = add / mul_coef 
      assert abs(add_n.value - mul1.value) ** 2 < ng.ATOM, (
          add_n.value,
          mul1.value,
      )
      assert abs(mul_n.value - add1.value) ** 2 < ng.ATOM, (
          mul_n.value,
          add1.value,
      )
      if mul_n in mul_to_add:
        add2 = mul_to_add[mul_n]
        sources = add2.comb.sources | add1.comb.sources
        node = ProofNode("DistTransferAdd", f"diff {add2} = {add1}", parents=list(sources))
        self.proof_steps.append(node)
        changed = self.elim_dist_add.force_zero(add2 - add1, cause=node) or changed
      else:
        mul_to_add[mul_n] = add1
        
      if add_n in add_to_mul:
        mul2 = add_to_mul[add_n]
        sources = mul2.comb.sources | mul1.comb.sources
        node = ProofNode("DistTransferMul", f"ratio {mul2} = {mul1}", parents=list(sources))
        self.proof_steps.append(node)
        changed = self.elim_dist_mul.force_one(mul2 / mul1, cause=node) or changed
      else:
        add_to_mul[add_n] = mul1

    return changed

  def transfer_dist_arc_mul(self):
    """Translate facts between equal distances and arc lengths (angles)."""
    changed = False
    for circle in self.circles:
      if len(circle.points) <= 3:
        continue
      dist_to_src = dict()
      arc_to_src = dict()
      for a in circle.points:
        for b in circle.points:
          if ng.orientation(a.value, b.value, circle.value.center) != 1:
            continue
          arc_obj, _ = self.get_arc(circle, a, b)
          arc_val = self.elim_angle.simplify(arc_obj)
          dist_obj = self.pair_to_dist_mul[a, b]
          dist_val = self.elim_dist_mul.simplify(dist_obj)
          
          if arc_val in arc_to_src:
            dist2 = arc_to_src[arc_val]
            sources = dist_obj.comb.sources | dist2.comb.sources | arc_val.comb.sources
            node = ProofNode("ArcToDist", f"chord {a}{b} ({dist_obj} = {dist2})", parents=list(sources))
            self.proof_steps.append(node)
            changed = self.elim_dist_mul.force_one(dist_obj / dist2, cause=node) or changed
          else:
            arc_to_src[arc_val] = dist_obj
            
          if dist_val in dist_to_src:
            arc2 = dist_to_src[dist_val]
            sources = arc_obj.comb.sources | arc2.comb.sources | dist_val.comb.sources
            node = ProofNode("DistToArc", f"arc {a}{b} ({arc_obj} = {arc2})", parents=list(sources))
            self.proof_steps.append(node)
            changed = self.elim_angle.force_zero(arc_obj - arc2, cause=node) or changed
          else:
            dist_to_src[dist_val] = arc_obj

    return changed

  def force_similar(self, triangle1, triangle2, cause=None):
    """Adds a fact that the two triangles are similar."""
    if (triangle1, triangle2) in self.known_similar:
      return False
    a, b, c = triangle1
    x, y, z = triangle2
    
    self.known_similar.add(((a, b, c), (x, y, z)))
    self.known_similar.add(((a, c, b), (x, z, y)))
    self.known_similar.add(((b, a, c), (y, x, z)))
    self.known_similar.add(((c, a, b), (z, x, y)))
    self.known_similar.add(((b, c, a), (y, z, x)))
    self.known_similar.add(((c, b, a), (z, y, x)))

    self.known_similar.add(((x, y, z), (a, b, c)))
    self.known_similar.add(((x, z, y), (a, c, b)))
    self.known_similar.add(((y, x, z), (b, a, c)))
    self.known_similar.add(((z, x, y), (c, a, b)))
    self.known_similar.add(((y, z, x), (b, c, a)))
    self.known_similar.add(((z, y, x), (c, b, a)))

    t1_rat1 = self.get_dist_ratio(a, b, a, c)
    t1_ang1 = self.get_point_angle(a, b, a, c)
    t1_rat2 = self.get_dist_ratio(a, b, b, c)
    t1_ang2 = self.get_point_angle(a, b, b, c)
    t2_rat1 = self.get_dist_ratio(x, y, x, z)
    t2_ang1 = self.get_point_angle(x, y, x, z)
    t2_rat2 = self.get_dist_ratio(x, y, y, z)
    t2_ang2 = self.get_point_angle(x, y, y, z)
    if ng.orientation(a.value, b.value, c.value) != ng.orientation(
        x.value, y.value, z.value
    ):
      t2_ang1 = -t2_ang1
      t2_ang2 = -t2_ang2
    else:
      pass

    changed = False
    changed = self.elim_angle.force_zero(t1_ang1 - t2_ang1, cause=cause) or changed
    changed = self.elim_angle.force_zero(t1_ang2 - t2_ang2, cause=cause) or changed
    changed = self.elim_dist_mul.force_one(t1_rat1 / t2_rat1, cause=cause) or changed
    changed = self.elim_dist_mul.force_one(t1_rat2 / t2_rat2, cause=cause) or changed

    return changed

  ########### Collinearity / concyclicity

  def force_collinear(self, points, cause=None):
    """Adds a fact that the given points are collinear."""
    assert len(points) > 1
    a = points[0]
    b = max(points, key=lambda b: ng.distance(a.value, b.value))
    c = max(points, key=lambda c: ng.distance(c.value, b.value))
    del a
    if self.num_identical(b, c):
      raise ValueError(
          'Collinearity predicate require at least two points to be distinct'
      )
    line1 = self.pair_to_line[b, c]
    if not all(line1.value.distance(point.value) < ng.ATOM for point in points):
      raise ValueError(
          'Points not numerically collinear: ' + ' '.join(map(str, points))
      )
    if set(line1.points) >= set(points):
      return False

    # find all the lines to be merged & all the points on them
    stack = list(points)
    points_set = set(line1.points)
    points = list(line1.points)
    lines = [line1]
    lines_set = set(lines)
    while stack:
      x = stack.pop()
      if x in points_set:
        continue
      for y in points:
        if self.num_identical(x, y):
          continue
        line = self.pair_to_line.get((x, y))
        if line in lines_set:
          continue
        lines.append(line)
        lines_set.add(line)
        stack.extend(line.points)
      points.append(x)
      points_set.add(x)

    points = sorted(points, key=lambda point: line1.value.position(point.value))

    # Aggregate sources from all merged lines + the new cause
    line_sources = set()
    if cause:
        line_sources.add(cause)
    for l in lines:
        line_sources.update(l.sources)

    # order the points
    main_line = FormalLine(
        points=points,
        main_pair=line1.main_pair,
        direction=line1.direction,
        value=line1.value,
        sources=line_sources # Pass aggregated sources
    )

    # additive segments on the line
    a = points[0]
    a1 = points[-1]
    for b, c in itertools.combinations(points[1:], 2):
      if self.num_identical(b, c):
        continue
      if self.num_identical(a, b):
        pos_b = self.pair_to_dist_add[a, a1] - self.pair_to_dist_add[a1, b]
      else:
        pos_b = self.pair_to_dist_add[a, b]
      if self.num_identical(a, c):
        pos_c = self.pair_to_dist_add[a, a1] - self.pair_to_dist_add[a1, c]
      else:
        pos_c = self.pair_to_dist_add[a, c]
      self.elim_dist_add.force_zero(
          pos_b + self.pair_to_dist_add[b, c] - pos_c, cause=cause
      )

    a, b = main_line.main_pair
    # glue the directions of the other lines
    for line in lines:
      self.elim_angle.force_zero(main_line.direction - line.direction, cause=cause)

    # replace the old lines with the new one
    self.lines.difference_update(lines)
    self.lines.add(main_line)
    for x, y in itertools.combinations(main_line.points, 2):
      if not self.num_identical(x, y):
        self.pair_to_line[x, y] = main_line
        self.pair_to_line[y, x] = main_line

    return True

  def force_concyclic(self, points, centers, cause=None):
    """Adds a fact that the points are concyclic (with optional center)."""

    # find all merged circles / points on them
    stack = list(points)
    points = []
    points_set = set()
    circles = []
    circles_set = set()
    while stack:
      a = stack.pop()
      if a in points_set:
        continue
      for b, c in itertools.combinations(points, 2):
        if self.num_identical(a, b):
          continue
        if self.num_identical(a, c):
          continue
        if self.num_identical(b, c):
          continue
        circle = self.triple_to_circle.get((a, b, c))
        if circle is None or circle in circles_set:
          continue
        if not circles:
          if set(circle.points) >= set(points + stack) and set(
              circle.centers
          ) >= set(centers):
            return False  # already satisfied
        circles.append(circle)
        circles_set.add(circle)
        stack.extend(circle.points)
      points_set.add(a)
      points.append(a)

    # numerically construct the circle
    if circles:
      defining_points = circles[0].defining_points
      circle_value = circles[0].value
    else:
      defining_points = []
      for x in points:
        if not any(self.num_identical(x, y) for y in defining_points):
          defining_points.append(x)
          if len(defining_points) == 3:
            break
      if len(defining_points) <= 2:
        raise ValueError('Need at least three different points on a circle')
      if centers:
        circle_value = NumCircle(
            center=centers[0].value,
            r=ng.distance(centers[0].value, points[0].value),
        )
      else:
        p1, p2, p3 = (x.value for x in defining_points)
        circle_value = NumCircle.through(p1, p2, p3)

    if not all(circle_value.distance(x.value) ** 2 < ng.ATOM for x in points):
      print([circle_value.distance(x.value) ** 2 for x in points])
      points_str = ' '.join(map(str, points))
      if centers:
        centers_str = ' Centers: ' + ' '.join(map(str, centers))
      else:
        centers_str = ''
      raise ValueError(
          'Points not numerically concyclic: ' + points_str + centers_str
      )

    centers = set(centers)
    for circle in circles:
      centers.update(circle.centers)
    centers = sorted(centers, key=lambda x: x.name)

    # Aggregate sources for the circle
    circle_sources = set()
    if cause:
        circle_sources.add(cause)
    for c in circles:
        circle_sources.update(c.sources)

    main_circle = FormalCircle(
        defining_points=defining_points,
        points=points,
        centers=centers,
        value=circle_value,
        sources=circle_sources # Pass aggregated sources
    )

    a, b, c = defining_points
    for x, y in itertools.combinations(points, 2):
      if self.num_identical(x, y):
        continue
      if x in (a, b, c):
        x, y = y, x
        if x in (a, b, c):
          continue
      if self.num_identical(x, c):
        y2 = b
      else:
        y2 = c
      ang = self.pair_to_dir[x, y2] - self.pair_to_dir[x, y]
      arc, _ = self.get_arc(main_circle, y, y2)
      self.elim_angle.force_zero(ang - arc, cause=cause)

    if centers:
      radius = self.get_dist_mul(points[0], centers[0])
      center = centers[0]
      for x in points[1:]:
        dist = self.get_dist_mul(x, center)
        self.elim_dist_mul.force_one(radius / dist, cause=cause)

    self.circles.difference_update(circles)
    self.circles.add(main_circle)
    for a in points:
      for b in points:
        if self.num_identical(a, b):
          continue
        for c in points:
          if self.num_identical(a, c):
            continue
          if self.num_identical(b, c):
            continue
          self.triple_to_circle[a, b, c] = main_circle

    return True

  def check_collinear(self, points):
    for a, b in itertools.combinations(points, 2):
      line = self.pair_to_line.get((a, b))
      if line is None:
        continue
      return set(points) <= set(line.points)

  def check_concyclic(self, points, centers=()):
    """Returns whether the points are known to be concyclic."""
    distinct_points = []
    for point in points:
      if any(self.num_identical(point, x) for x in distinct_points):
        continue
      distinct_points.append(point)
    if len(distinct_points) < 3:
      raise ValueError('Need at least three numerically distinct points')

    circle = self.triple_to_circle.get(tuple(distinct_points[:3]))

    if circle is None:
      return False
    if not set(centers) <= set(circle.centers):
      return False
    if not set(points) <= set(circle.points):
      return False

    return True

  ############# Point merging

  def force_equal_points(self, a, b, cause=None):
      """Merges two given points (they are provably equal)."""
      a = self.point_subst[a]
      b = self.point_subst[b]
      if a == b:
        return False

      # merge in lines
      for line in list(self.lines):
        has_a = a in line.points
        has_b = b in line.points
        if has_a == has_b:
          continue
        points = list(line.points)
        if not has_a:
          points.append(a)
        else:
          points.append(b)
        self.force_collinear(points, cause=cause)

      for line in list(self.lines):
        if b in line.points:
          main_pair = line.main_pair
          direction = line.direction
          if b in main_pair:
            if b == main_pair[0]:
              main_pair = a, main_pair[1]
            else:
              main_pair = main_pair[0], a
          
          # [Fix]: Propagate sources when re-creating lines during point merge
          line2 = FormalLine(
              points=[x for x in line.points if x != b],
              main_pair=main_pair,
              direction=direction,
              value=line.value,
              sources=line.sources
          )
          for x, y in itertools.permutations(line2.points, 2):
            if not self.num_identical(x, y):
              self.pair_to_line[x, y] = line2
          self.lines.remove(line)
          self.lines.add(line2)

      # merge in circles
      for circle in list(self.circles):
        has_a = a in circle.points
        has_b = b in circle.points
        if has_a == has_b:
          continue
        points = list(circle.points)
        if not has_a:
          points.append(a)
        else:
          points.append(b)
        self.force_concyclic(points, circle.centers, cause=cause)
      for circle in list(self.circles):
        if b in circle.points or b in circle.centers:
          defining_points = circle.defining_points
          if b in defining_points:
            defining_points = [(x if x != b else a) for x in defining_points]
          
          # Propagate sources when re-creating circles during point merge
          circle2 = FormalCircle(
              defining_points=defining_points,
              points=[x for x in circle.points if x != b],
              centers=[x for x in circle.centers if x != b],
              value=circle.value,
              sources=circle.sources
          )
          for x, y, z in itertools.permutations(circle2.points, 3):
            if self.num_identical(x, y):
              continue
            if self.num_identical(y, z):
              continue
            if self.num_identical(z, x):
              continue
            self.triple_to_circle[x, y, z] = circle2
          self.circles.remove(circle)
          self.circles.add(circle2)

      # merge in distances
      for x in self.points:
        if x == a or x == b:
          continue
        if not self.num_identical(x, a) and not self.num_identical(x, b):
          d1 = self.pair_to_dist_mul[x, a]
          d2 = self.pair_to_dist_mul[x, b]
          self.elim_dist_mul.force_one(d1 / d2, cause=cause)

      # remove 'b' from occuring in self.points

      self.point_subst = {
          x: y if y != b else a for x, y in self.point_subst.items()
      }

      self.points = [x for x in self.points if x != b]

  def check_equal_points(self, a, b):
    a = self.point_subst[a]
    b = self.point_subst[b]
    return a == b

  #######  low-level functions

  def update_cache(self):
    for a, b in itertools.combinations(self.points, 2):
      if self.num_identical(a, b):
        continue
      dist = self.get_dist_mul(a, b)
      self.dist_mul_cache[a, b] = dist
      self.dist_mul_cache[b, a] = dist
      direction = self.elim_angle.simplify(self.pair_to_dir[a, b])
      self.direction_cache[a, b] = direction
      self.direction_cache[b, a] = direction

  def get_dist_ratio(self, a, b, c, d):
    return self.dist_mul_cache[c, d] / self.dist_mul_cache[a, b]

  def get_point_angle(self, a, b, c, d):
    return self.direction_cache[c, d] - self.direction_cache[a, b]

  def get_dist_mul(self, a, b):
    dist_mul = self.pair_to_dist_mul[a, b]
    return self.elim_dist_mul.simplify(dist_mul)

  def get_dist_add(self, a, b):
    dist_add = self.pair_to_dist_add[a, b]
    return self.elim_dist_add.simplify(dist_add)

  def get_point_dir(self, a, b):
    return self.elim_angle.simplify(self.pair_to_dir[a, b])

  def get_arc(self, circle, a, b):
    c = next(
        c
        for c in circle.defining_points
        if not (self.num_identical(a, c) or self.num_identical(b, c))
    )
    ang = self.pair_to_dir[b, c] - self.pair_to_dir[a, c]
    return ang, c

  # debugging

  def lines_sanity_check(self):
    lines_set = set()
    for a, b in itertools.combinations(self.points, 2):
      if not self.num_identical(a, b):
        lines_set.add(self.pair_to_line[a, b])
    assert lines_set == self.lines
    for line in lines_set:
      for a, b in itertools.combinations(line.points, 2):
        if self.num_identical(a, b):
          continue
        assert line == self.pair_to_line[a, b]
        assert line == self.pair_to_line[b, a]
