
"""
Shuttle Bus Solver – User-Debugged & Top-K Matching Heuristic
=============================================================
* All user-identified bugs fixed (Deadhead rules, Wage calc, Time loops).
* Combinatorial explosion fixed via Top-K wp2 matching (keeps runtime < 1 min).
* MAX_IDLE strictly set to 120 with NO truncation on successors.
"""

import json, sys, time, bisect
from collections import defaultdict

try:
    import gurobipy as gp
    from gurobipy import GRB
except ImportError:
    sys.exit("gurobipy not found.")

def ceil15(x):   return ((x + 14) // 15) * 15
def floor15(x):  return (x // 15) * 15

def make_tt(legs, buckets):
    leg_idx = {l: i for i, l in enumerate(legs)}
    bkt = [(b['from_min'], b['to_min'], b['minutes']) for b in buckets]
    cache = {}
    def tt(o, d, s):
        if o == d: return 0
        k = (o, d, s)
        if k in cache: return cache[k]
        leg = f"{o}-{d}"
        if leg not in leg_idx: return 0
        idx = leg_idx[leg]
        v = int(bkt[-1][2][idx])
        for f, t, mins in bkt:
            if f <= s < t: v = int(mins[idx]); break
        cache[k] = v
        return v
    return tt

class Trip:
    __slots__ = ('id', 'numeric_id', 'origin', 'dest', 'start', 'end')
    def __init__(self, d, tt):
        self.id         = d['trip_id']
        self.numeric_id = int(''.join(filter(str.isdigit, str(self.id)))) 
        self.origin     = d['origin']
        self.dest       = d['destination']
        self.start      = int(d['departure_min'])
        self.end        = self.start + tt(self.origin, self.dest, self.start)

# באג 2 תוקן: הסף העליון לשעות רגילות קשיח על 8 שעות (480 דקות) כחוק.
def driver_wage(s0, s1, c_reg, c_ot):
    paid = s1 - s0                                      
    reg  = min(paid, 480)                 
    ot   = max(0, paid - 480)
    return (reg / 60) * c_reg + (ot / 60) * c_ot

def generate_fast_duties(trips, params, tt):
    t_start = time.time()
    
    alpha   = int(params['break_min_from_start_hours'] * 60)   
    beta    = int(params['break_min_from_end_hours']   * 60)   
    b_len   = int(params['break_length_hours']         * 60)   
    L_min   = int(params['shift_min_hours'] * 60)                                
    L_max   = int(params['shift_max_hours'] * 60)                                
    c_reg   = params['cost_driver_regular_per_h']
    c_ot    = params['cost_driver_overtime_per_h']
    
    # באג 3 תוקן: קורא רק את cost_variable_per_min עם 0.0 כגיבוי בטוח.
    c_var   = float(params.get('cost_variable_per_min', 0.0))

    MAX_IDLE = 120 # זמן המתנה מקסימלי
    MAX_WP_TIME = L_max - b_len - beta 
    
    adj = defaultdict(list)
    for u in trips:
        for v in trips:
            if u.id != v.id and u.dest == v.origin:
                gap = v.start - u.end
                # באג 5 תוקן: אין יותר [2:], נכנסים כל ההמשכים החוקיים עד שעתיים
                if 0 <= gap <= MAX_IDLE:
                    adj[u.id].append(v)
                
    workpieces = []
    def dfs(trip, path):
        workpieces.append(list(path))
        if path[-1].end - path[0].start >= MAX_WP_TIME: return
        for nxt in adj[trip.id]:
            if nxt.start >= path[-1].end:   
                path.append(nxt)
                dfs(nxt, path)
                path.pop()

    for t in trips: dfs(t, [t])
    print(f"    [Timer] DFS Phase generated {len(workpieces)} wp's in {time.time() - t_start:.3f}s")

    t_match = time.time()
    
    wp_data = []
    for wp in workpieces:
        mask = 0
        for tr in wp: mask |= (1 << tr.numeric_id)
        wp_data.append({'wp': wp, 'mask': mask, 'start': wp[0].start, 'end': wp[-1].end})
        
    wp_data.sort(key=lambda d: d['start'])
    wp_starts = [d['start'] for d in wp_data] 
    
    best_cost = {}
    def record(trip_ids, acts, s0, s1, b0, b1, bloc, cost):
        sig = (tuple(sorted(trip_ids)), bloc, s0, b0) 
        if sig not in best_cost or cost < best_cost[sig]['cost']:
            best_cost[sig] = {
                'trips':    list(trip_ids),
                'acts':     acts,
                's0': s0, 's1': s1, 'b0': b0, 'b1': b1, 'bloc': bloc,
                'cost':     cost,
                'dwells_A': [(a['start_min'],a['end_min']) for a in acts if a['type'] in ('wait','break') and a.get('at')=='A'],
                'dwells_B': [(a['start_min'],a['end_min']) for a in acts if a['type'] in ('wait','break') and a.get('at')=='B'],
            }

    MAX_SPAN = L_max - b_len 
    TOP_K_MATCHES = 10 # יוריסטיקת המהירות: לוקח רק את ה-10 המשכים שהכי "צמודים" לזמן ההפסקה

    for data1 in wp_data:
        wp1, mask1 = data1['wp'], data1['mask']
        s0_target = wp1[0].start - tt('D', wp1[0].origin, max(0, wp1[0].start - 60))
        s0_upper = floor15(s0_target)
        s0_options = [s0_upper, s0_upper - 15]
        
        min_wp2_start = data1['end'] + b_len
        idx = bisect.bisect_left(wp_starts, min_wp2_start)
        
        # אוספים את כל ההמשכים החוקיים
        possible_wp2s = []
        for data2 in wp_data[idx:]:
            if data2['end'] - wp1[0].start > MAX_SPAN: continue 
            if mask1 & data2['mask']: continue
            gap = data2['start'] - min_wp2_start
            possible_wp2s.append((gap, data2['wp']))

        # ממיינים לפי הפער (מהקצר לארוך) ולוקחים רק את ה-TOP 10
        possible_wp2s.sort(key=lambda x: x[0])
        valid_wp2s = [None] + [w for g, w in possible_wp2s[:TOP_K_MATCHES]]

        for s0 in s0_options:
            if s0 + tt('D', wp1[0].origin, s0) > wp1[0].start: continue

            for wp2 in valid_wp2s:
                for bloc in ['A', 'B', 'D']:
                    acts = []
                    t = s0; loc = 'D'; total_dh = 0

                    def dh(frm, to, depart):
                        nonlocal t, loc, total_dh
                        dur = tt(frm, to, depart)
                        if dur > 0:
                            acts.append({"type":"deadhead","from":frm,"to":to,"start_min":depart,"end_min":depart+dur})
                            total_dh += dur
                        t = depart + dur; loc = to

                    def wt(loc_at, until):
                        nonlocal t
                        if until > t:
                            acts.append({"type":"wait","at":loc_at,"start_min":t,"end_min":until})
                            t = until

                    # WP1
                    dh('D', wp1[0].origin, t)
                    for tr in wp1:
                        wt(tr.origin, tr.start)
                        acts.append({"type":"service","trip_id":tr.id,"start_min":tr.start,"end_min":tr.end})
                        t = tr.end; loc = tr.dest

                    # Break
                    b0_earliest = s0 + alpha
                    
                    # באג 1 תוקן: הגעה חוקית דרך D להפסקה
                    if loc != bloc:
                        if loc != 'D': dh(loc, 'D', t)
                        if bloc != 'D': dh('D', bloc, t)
                        
                    b0_raw = max(b0_earliest, t)
                    b0 = ceil15(b0_raw)
                    b1 = b0 + b_len

                    latest_b0 = s0 + L_max - beta - b_len
                    if wp2: latest_b0 = min(latest_b0, wp2[0].start - tt(bloc, wp2[0].origin, max(0, b1)) - b_len)

                    if b0 > latest_b0: continue

                    wt(bloc, b0)
                    acts.append({"type":"break","at":bloc,"start_min":b0,"end_min":b1})
                    t = b1; loc = bloc

                    # WP2
                    if wp2:
                        # באג 1 תוקן: הגעה חוקית דרך D לתחילת החצי השני
                        next_loc = wp2[0].origin
                        if loc != next_loc:
                            if loc != 'D': dh(loc, 'D', t)
                            if next_loc != 'D': dh('D', next_loc, t)
                            
                        for tr in wp2:
                            wt(tr.origin, tr.start)
                            acts.append({"type":"service","trip_id":tr.id,"start_min":tr.start,"end_min":tr.end})
                            t = tr.end; loc = tr.dest

                    s1_min = ceil15(max(s0 + L_min, b1 + beta))
                    s1_max = s0 + L_max
                    if s1_min > s1_max: continue

                    best_s1 = None; best_dh_st = None; best_c = float('inf')

                    # באג 4 תוקן: דילוג מסודר על s1 קטנים מדי למניעת Range ריק
                    for s1 in range(s1_min, s1_max + 1, 15):
                        if s1 < t: continue
                        
                        dh_st = -1
                        for cand in range(s1, t - 1, -1):
                            if cand + tt(loc, 'D', cand) <= s1:
                                dh_st = cand; break
                        if dh_st == -1:
                            if t + tt(loc, 'D', t) <= s1: dh_st = t
                            else: continue

                        c = driver_wage(s0, s1, c_reg, c_ot)
                        if c < best_c:
                            best_c = c; best_s1 = s1; best_dh_st = dh_st
                            break

                    if best_s1 is None: continue

                    wt(loc, best_dh_st)
                    
                    # חזרה לדיפו בסוף היום
                    if loc != 'D': dh(loc, 'D', best_dh_st)
                    if t < best_s1: wt('D', best_s1)

                    final_cost = best_c + (total_dh * c_var)
                    trip_ids = [tr.id for tr in wp1]
                    if wp2: trip_ids.extend([tr.id for tr in wp2])
                    
                    record(trip_ids, acts, s0, best_s1, b0, b1, bloc, final_cost)

    print(f"    [Timer] Top-K Matching took {time.time() - t_match:.3f}s")
    return list(best_cost.values())

def solve(duties, all_trip_ids, params):
    t_setup = time.time()
    c_fix = params['cost_fixed_vehicle']
    cap   = params['terminal_capacity']

    K = len(duties)
    T = len(all_trip_ids)
    print(f"    [Timer] Setup Phase 2 variables took {time.time() - t_setup:.3f}s")
    
    m = gp.Model("ShuttleBus_TopK")
    m.Params.TimeLimit  = 120     # גורובי מוגבל ל-2 דקות גג
    m.Params.MIPFocus   = 1       
    m.Params.MIPGap     = 0.005   
    m.Params.OutputFlag = 1

    t_model = time.time()
    y     = m.addVars(K,        vtype=GRB.BINARY,     name="y")
    dummy = m.addVars(T,        vtype=GRB.CONTINUOUS, lb=0, name="slack")
    V     = m.addVar(           vtype=GRB.INTEGER,    lb=0, name="V")

    PENALTY = 500_000
    m.setObjective(
        c_fix * V + gp.quicksum(duties[k]['cost'] * y[k] for k in range(K)) + gp.quicksum(PENALTY * dummy[i] for i in range(T)),
        GRB.MINIMIZE
    )

    tid2i = {t: i for i, t in enumerate(all_trip_ids)}
    for t_id in all_trip_ids:
        i = tid2i[t_id]
        covers = [k for k in range(K) if t_id in duties[k]['trips']]
        m.addConstr(gp.quicksum(y[k] for k in covers) + dummy[i] == 1, f"cov_{t_id}")

    events = sorted({d['s0'] for d in duties} | {d['s1'] for d in duties})
    for ev in events:
        active = [k for k in range(K) if duties[k]['s0'] <= ev < duties[k]['s1']]
        if active: m.addConstr(gp.quicksum(y[k] for k in active) <= V, f"veh_{ev}")

    for loc, attr in (('A','dwells_A'), ('B','dwells_B')):
        times = sorted({st for d in duties for st,_ in d[attr]})
        for ev in times:
            dwell = [k for k in range(K) if any(st <= ev < et for st,et in duties[k][attr])]
            if dwell: m.addConstr(gp.quicksum(y[k] for k in dwell) <= cap, f"cap_{loc}_{ev}")
    
    print(f"    [Timer] Gurobi Model Construction took {time.time() - t_model:.3f}s")

    t_opt = time.time()
    m.optimize()
    print(f"    [Timer] Gurobi Optimization Phase took {time.time() - t_opt:.3f}s")

    if m.Status not in (GRB.OPTIMAL, GRB.TIME_LIMIT, GRB.SUBOPTIMAL): return None, None
    sel   = [duties[k] for k in range(K) if y[k].X > 0.5]
    uncov = [all_trip_ids[i] for i in range(T) if dummy[i].X > 0.5]
    return sel, uncov

def assign_vehicles(sel):
    sel = sorted(sel, key=lambda d: d['s0'])
    free = []   
    for d in sel:
        reuse = next((i for i,(ft,_) in enumerate(free) if d['s0'] >= ft), None)
        if reuse is None:
            lbl = f"v{len(free)+1}"
            free.append((d['s1'], lbl))
        else:
            _, lbl = free[reuse]
            free[reuse] = (d['s1'], lbl)
        d['vehicle_id'] = lbl
    return sel

def dh_cost(acts, c_var):
    return sum((a['end_min']-a['start_min']) for a in acts if a['type']=='deadhead') * c_var

def main():
    fp = sys.argv[1] if len(sys.argv) > 1 else "small_01.json"
    inst = fp.rsplit('.',1)[0]

    print(f"\n{'='*60}")
    print(f"  Shuttle Bus Solver (User Fixed + TopK) |  {fp}")
    print(f"{'='*60}")

    with open(fp, encoding='utf-8') as f: data = json.load(f)

    params = data['parameters']
    tt     = make_tt(data['travel_time']['legs'], data['travel_time']['buckets'])
    trips  = sorted([Trip(t, tt) for t in data['trips']], key=lambda x: x.start)
    tids   = [t.id for t in trips]

    t_global = time.time()

    print("\n[Phase 1] Generating Duties...")
    duties = generate_fast_duties(trips, params, tt)
    
    if not duties: print("No duties generated."); return

    print(f"\n[Phase 2] MILP Optimization...")
    sel, uncov = solve(duties, tids, params)

    if sel is None: print("No feasible MILP solution."); return

    if uncov: print(f"  *** UNCOVERED TRIPS: {uncov} ***")
    else: print("  All trips covered successfully!")

    sel = assign_vehicles(sel)
    n_v = len({d['vehicle_id'] for d in sel})

    out_duties = []
    for i, d in enumerate(sorted(sel, key=lambda x: x['s0'])):
        out_duties.append({
            "duty_id": f"k{i+1}", "driver_id": f"d{i+1}", "vehicle_id": d['vehicle_id'],
            "shift_start_min": d['s0'], "shift_end_min": d['s1'], "break_start_min": d['b0'],
            "break_end_min": d['b1'], "break_location": d['bloc'], "activities": d['acts']
        })

    out = {"instance_id": inst, "duties": out_duties}
    out_fp = f"solution_{fp}"
    with open(out_fp, 'w', encoding='utf-8') as f: json.dump(out, f, indent=2, ensure_ascii=False)

    c_fix   = params['cost_fixed_vehicle']
    c_var   = float(params.get('cost_variable_per_min', 0.0))
    c_reg   = params['cost_driver_regular_per_h']
    c_ot    = params['cost_driver_overtime_per_h']

    veh_cost    = n_v * c_fix
    driver_cost = sum(driver_wage(d['s0'],d['s1'],c_reg,c_ot) for d in sel)
    dh_cost_tot = sum(dh_cost(d['acts'],c_var) for d in sel)
    total       = veh_cost + driver_cost + dh_cost_tot

    print(f"\n{'='*60}")
    print(f"  RESULTS")
    print(f"  Vehicles : {n_v} × {c_fix} = {veh_cost}")
    print(f"  Driver   : {driver_cost:.2f}")
    print(f"  Deadhead : {dh_cost_tot:.2f}")
    print(f"  TOTAL    : {total:.2f} ILS")
    print(f"  Total Wall time: {time.time()-t_global:.1f}s")
    print(f"{'='*60}")

if __name__ == "__main__":
    main()