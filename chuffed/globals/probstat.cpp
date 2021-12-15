#include <chuffed/core/propagator.h>
#include <stdlib.h>
#include <cfenv>

#include <iostream>

using namespace std;

//int ccc = 0;

class VarianceInt : public Propagator {
public:
  int const N;
  IntVar *y;
  vec<IntVar *> x;
  IntVar *s; // s = sum(x)
  int scale;
  int mode;
  int counter_prop;

  Tint ub_idx = NULL;
  Tint lb_idx = NULL;

  vec<Tint> pos; // if the x's are below (-1), overlapping (0) or above (1) the
                 // mean of lb variance. 2 for unknown.
  Tint64_t Mx; // lowest sum of lb n^3 variance
  Tint64_t MxR; // highest sum of lb n^3 variance
  Tint64_t Vx; // lb n^3 variance
  Tint all_fixed; // true if all x are fixed
  Tint n_fixed;
  Tint one_fixed;
  Tint subsumed;
  Tint64_t glb; // warning: not kept up to date if lub <= glb
  Tint64_t lub; // dito

  // Statistics
  uint64_t n_wakeups;
  uint64_t n_runs;
  uint64_t n_prop_v_lb;
  uint64_t n_incons_v_lb;
  uint64_t n_prop_v_fix;
  uint64_t n_incons_v_fix;
  uint64_t n_prop_x_above;
  uint64_t n_incons_x_above;
  int64_t x_above_max_strength;
  uint64_t n_prop_x_below;
  uint64_t n_incons_x_below;
  int64_t x_below_max_strength;
  uint64_t n_prop_x_overlap;
  uint64_t n_incons_x_overlap;
  int64_t x_overlap_max_strength;
  uint64_t n_prop_x;
  uint64_t n_incons_x;
  uint64_t n_prop_v;
  uint64_t n_incons_v;

  VarianceInt(IntVar *_y, vec<IntVar *> &_x, IntVar *_s, int _scale, int _mode) :
      N(_x.size()), y(_y), x(_x), s(_s), scale(_scale), mode(_mode),
      n_wakeups(0), n_runs(0), n_prop_v_lb(0), n_incons_v_lb(0),
      n_prop_v_fix(0), n_incons_v_fix(0), n_prop_x_above(0),
      n_incons_x_above(0), n_prop_x_below(0), n_incons_x_below(0),
      n_prop_x_overlap(0), n_incons_x_overlap(0), n_prop_x(0), n_incons_x(0),
      n_prop_v(0), n_incons_v(0),
      x_above_max_strength(INT64_MIN), x_below_max_strength(INT64_MIN),
      x_overlap_max_strength(INT64_MIN) {
    priority = 3;
    all_fixed = 0;
    subsumed = 0;
    switch (mode) {
      case 1: // version 1
      case 2: // version 1 approx c
      case 3: // version 2
      case 4: // version 2 approx c
      case 5: // only lb var
      case 7: // smart
      case 8: // only new lb var
      case 9: // real version
        init_v1v2();
        break;
      case 6:
        init_dc();
        break;
      default: // checking x, filter v
        init_checking();
    }
  }

  void wakeup(int i, int c) override {
    if (subsumed) return;
    n_wakeups++;

    if (!all_fixed && i < N && c & EVENT_F) {
      n_fixed++;
      if (n_fixed == N)
        all_fixed = 1;
      //int all_fixed_ = 1;
      //for (int i = 0; i < N; i++) { // O(N)
      //  if (!x[i]->isFixed()) {
      //    all_fixed_ = 0;
      //    break;
      //  }
      //}
      //all_fixed = all_fixed_;
    }

    if (mode == 9 && glb <= lub) { // Trivial case: var >= 0;
      if (i < N && c & EVENT_U && x[i]->getMax() < lub)
        lub = x[i]->getMax();
      if (i < N && c & EVENT_L && x[i]->getMin() > glb)
        glb = x[i]->getMin();
      if (glb > lub)
        pushInQueue(); // something of use can be done
      return;
    }

    if (!all_fixed && mode == 9 && i < N) { // FIXME fix if run again
      int64_t xlb = N*x[i]->getMin();
      int64_t xub = N*x[i]->getMax();
      if (c & EVENT_U) {
        if (Mx <= xlb) return;
        else if (Mx <= xub) return;
        else pushInQueue();
      } else if (c & EVENT_L) {
        if (xub <= Mx) return;
        else if (xlb <= Mx) return;
        else pushInQueue();
      }
    }

    pushInQueue();
  }

  bool propagate() override {
//    printf("%% running propagate\n");
    n_runs++;
    if (all_fixed && mode != 6) return checking_prop();
    switch (mode) {
      case 1: // version 1
        return prop_var_lb()  &&  prop_x_v1();
      case 2: // version 1 approx c
        return prop_var_lb()  &&  prop_x_v1x();
      case 3: // version 2
        return prop_var_lb()  &&  prop_x_v2();
      case 4: // version 2 approx c
        return prop_var_lb()  &&  prop_x_v2x();
      case 5:
        return prop_var_lb();
      case 6:
        return prop_x_dc();
      case 7:
        return prop_var_lb()  &&  prop_x_v7();
      case 8: //
        return prop_var_lb_new();
      case 9: // Real version (as in paper)
        return prop_var_lb_real();
      default: // checking x, filter v
        return checking_prop();
    }
  }

  void printStats() override {
    fprintf(stderr, "%% Spread propagator statistics");
    fprintf(stderr, " for mode %d\n", mode);
    fprintf(stderr, ":\n");
    fprintf(stderr, "%%\t#wakeups: %lld\n", n_wakeups);
    fprintf(stderr, "%%\t#runs: %lld\n", n_runs);
    fprintf(stderr, "%%\t#prop var: %lld\n", n_prop_v);
    fprintf(stderr, "%%\t#fail var: %lld\n", n_incons_v);
    fprintf(stderr, "%%\t#prop var lb: %lld\n", n_prop_v_lb);
    fprintf(stderr, "%%\t#fail var lb: %lld\n", n_incons_v_lb);
    fprintf(stderr, "%%\t#prop var fixed x: %lld\n", n_prop_v_fix);
    fprintf(stderr, "%%\t#fail var fixed x: %lld\n", n_incons_v_fix);
    fprintf(stderr, "%%\t#prop x: %lld\n", n_prop_x);
    fprintf(stderr, "%%\t#fail x: %lld\n", n_incons_x);
    fprintf(stderr, "%%\t#prop x above: %lld\n", n_prop_x_above);
    fprintf(stderr, "%%\t#fail x above: %lld\n", n_incons_x_above);
    fprintf(stderr, "%%\t#x above max strength: %lld\n", x_above_max_strength);
    fprintf(stderr, "%%\t#prop x below: %lld\n", n_prop_x_below);
    fprintf(stderr, "%%\t#fail x below: %lld\n", n_incons_x_below);
    fprintf(stderr, "%%\t#x below max strength: %lld\n", x_below_max_strength);
    fprintf(stderr, "%%\t#prop x overlap: %lld\n", n_prop_x_overlap);
    fprintf(stderr, "%%\t#fail x overlap: %lld\n", n_incons_x_overlap);
    fprintf(stderr, "%%\t#x overlap max strength: %lld\n", x_overlap_max_strength);
  }

  int64_t lli_max(int64_t a, int64_t b) {
    return a > b ? a : b;
  }

  //------------------//
  // Checking Version // mode = 0
  //------------------//

  void init_checking() {
    for (int i = 0; i < N; i++) x[i]->attach(this, i, EVENT_F);
    y->attach(this, N, EVENT_F);
    int n_fixed_ = 0;
    for (int i = 0; i < N; ++i) {
      if (x[i]->isFixed()) n_fixed_++;
    }
    n_fixed = n_fixed_;
  }

  bool checking_prop() {
//    printf("%% running checking_prop\n");

    //printf("%% Fixed Proping! variance = %d..%d \n", y->getMin(), y->getMax());
    // only propagate if all fixed
    if (!all_fixed) return true;

    // N*mean
    int64_t sumx = 0;
    for (int i = 0; i < N; i++) {
//      printf("%% asdasd");
//      printf("%% x[%d] = %d..%d\n", i, x[i]->getMin(), x[i]->getMax());
//      printf("%% x[%d] = %d\n", i, x[i]->getVal());
      sumx += x[i]->getVal();
    }

    // N*N * squared diff
    int64_t sqdiff = 0;
    for (int i = 0; i < N; i++) {
      int64_t diff = N * x[i]->getVal() - sumx;
      sqdiff += diff * diff;
    }

    // result
    long double result_f = (long double) sqdiff / (long double) (N*N*N);
    int64_t result = (int64_t) (result_f * scale);

//    printf("%% Fixed X Prop %%\n");
//    for (int i = 0; i < N; ++i) printf("   %% x[%d] = %d..%d      ", i, x[i]->getMin(), x[i]->getMax());
//    printf("%% y = %d..%d      ", y->getMin(), y->getMax());
//    printf("%% s = %d..%d\n", s->getMin(), s->getMax());
//    printf("   %% sqdiff = %lld and result_f = %Lf and result_f scaled = %Lf and result = %lld", sqdiff, result_f, result_f * scale, result);
//    printf("   %% want to set y to %lli when it is %d..%d\n", result, y->getMin(), y->getMax());

    // set y
    if(y->setValNotR(result)) {
      n_prop_v_fix++;
      Clause* r = nullptr;
      if(so.lazy) {
        // Set up reason
        r = Reason_new(N+1);
        for(int ii = 0; ii < N; ++ii) { (*r)[ii+1] = x[ii]->getValLit(); }
      }
      if(!y->setVal(result, r)) {
        n_incons_v_fix++;
        return false;
      }
    }
    subsumed = 1;
    return true;
  }

  //-----------//
  // Version 1 // mode = 1
  //-----------//

  void init_v1v2() {
    pos.growTo(N);
    for (int i = 0; i < N; ++i) pos[i] = 2;
    for (int i = 0; i < N; i++) {
      x[i]->attach(this, i, EVENT_LU);
    }
    y->attach(this, N, EVENT_F);
    s->attach(this, N+1, EVENT_LU);

    if (mode == 9) {
      int64_t lub_ = INT64_MAX;
      int64_t glb_ = INT64_MIN;
      for (int i = 0; i < N; ++i) {
        if (x[i]->getMin() > glb_) glb_ = x[i]->getMin();
        if (x[i]->getMax() < lub_) lub_ = x[i]->getMax();
      }
      lub = lub_;
      glb = glb_;
    }

    int n_fixed_ = 0;
    for (int i = 0; i < N; ++i) {
      if (x[i]->isFixed()) n_fixed_++;
    }
    n_fixed = n_fixed_;
  }

  bool prop_var_lb() {
//    printf("%% running prop_var_lb\n");
    int64_t L = s->getMin(), R = s->getMax();

    // Binary Chop
    while (L <= R) { // O(log sup x - inf x)

//      printf("%% ~~~~> ~~~~> M = %d..%d,   L = %lli,    R = %lli\n", s->getMin(), s->getMax(), L, R);

      int64_t m = (L + R) / 2;
      m = m - (m < 0); // round down
      int64_t mR = m + 1; // round up to next
      if (m < L || R < m) m = L;
      if (mR < L || R < mR) mR = R;
      if (L + 1 == R) {
        m = L; mR = R;
      } // FIXME? d = (R - L) / 2;  m = L+d, mR = m+1

      // calculate variance
      int64_t var = 0, varR = 0;
      for (auto i = 0; i < N; ++i) { // O(N)
        int64_t lb = N * x[i]->getMin(), ub = N * x[i]->getMax();
        if (m < lb)      var += (lb - m) * (lb - m);
        else if (ub < m) var += (ub - m) * (ub - m);
        if (mR < lb)      varR += (lb - mR) * (lb - mR);
        else if (ub < mR) varR += (ub - mR) * (ub - mR);
      }

      // terminate
      if (var == 0 || varR == 0) {
//        return true;
        if (var > varR) {
          var = varR; m = mR;
        }
        Vx = var;

        auto mL = m-1;
        for (; mL > s->getMin(); --mL){
          int var_temp = 0;
          for (auto i = 0; i < N; ++i) { // O(N)
            int64_t lb = N * x[i]->getMin(), ub = N * x[i]->getMax();
            if (mL < lb)      var_temp += (lb - mL) * (lb - mL);
            else if (ub < mL) var_temp += (ub - mL) * (ub - mL);
          }
          if (var != var_temp) {
            break;
          }
        }
        ++mL;
        Mx = mL;

        auto mR = m+1;
        for (; mR < s->getMax(); ++mR){
          int var_temp = 0;
          for (auto i = 0; i < N; ++i) { // O(N)
            int64_t lb = N * x[i]->getMin(), ub = N * x[i]->getMax();
            if (mR < lb)      var_temp += (lb - mR) * (lb - mR);
            else if (ub < mR) var_temp += (ub - mR) * (ub - mR);
          }
          if (var != var_temp) {
            break;
          }
        }
        --mR;
        MxR = mR;

        break;
      }

      // iterate
      if (var > varR && R > mR) L = mR;
      else if (var < varR && L < m) R = m;

      // exit loop for propagation
      else {
        if (var > varR) {
          var = varR; m = mR;
        }
        Vx = var;

        auto mL = m-1;
        for (; mL > s->getMin(); --mL){
          int var_temp = 0;
          for (auto i = 0; i < N; ++i) { // O(N)
            int64_t lb = N * x[i]->getMin(), ub = N * x[i]->getMax();
            if (mL < lb)      var_temp += (lb - mL) * (lb - mL);
            else if (ub < mL) var_temp += (ub - mL) * (ub - mL);
          }
          if (var != var_temp) {
            break;
          }
        }
        ++mL;
        Mx = mL;

        auto mR = m+1;
        for (; mR < s->getMax(); ++mR){
          int var_temp = 0;
          for (auto i = 0; i < N; ++i) { // O(N)
            int64_t lb = N * x[i]->getMin(), ub = N * x[i]->getMax();
            if (mR < lb)      var_temp += (lb - mR) * (lb - mR);
            else if (ub < mR) var_temp += (ub - mR) * (ub - mR);
          }
          if (var != var_temp) {
            break;
          }
        }
        --mR;
        MxR = mR;

        break;
      }
    }

    // update positions
    for (int i = 0; i < N; ++i) { // O(N)
      if (MxR < N*x[i]->getMin())     pos[i] =  1; // TODO: changed to MxR from Mx, correct?
      else if (N*x[i]->getMax() < Mx) pos[i] = -1;
      else                            pos[i] =  0;
    }

    // calculate variance lb
    const int reset = std::fegetround();
    std::fesetround(FE_DOWNWARD);
    long double variance_f = (long double) Vx / (long double) (N*N*N);
    auto variance = (int64_t) (variance_f * scale);
    std:fesetround(reset);

    // set y
    if(y->setMinNotR(variance)) {
      n_prop_v_lb++;
      Clause* r = nullptr;
      if(so.lazy) {
        // Set up reason
        Lit lit[2*N+2];
        int lits = 0;
        for(int ii = 0; ii < N; ++ii) {
          if (pos[ii] == 1)       lit[lits++] = x[ii]->getMinLit(); // TODO: changed to MxR from Mx, correct?
          else if (pos[ii] == -1) lit[lits++] = x[ii]->getMaxLit();
        }
        if (Mx == s->getMin()) lit[lits++] = s->getMinLit();
        if (MxR == s->getMax()) lit[lits++] = s->getMaxLit(); // TODO: changed to MxR from Mx, correct?
        r = Reason_new(lits+1);
        for(int ii = 0; ii < lits; ++ii) (*r)[ii+1] = lit[ii];
      }
      if(!y->setMin(variance, r)) {
        n_incons_v_lb++;
        return false;
      }
    }
    return true;
  }

  bool prop_x_v1() {
    int n_AuB = N;
    for (int j = 0; j < N; j++) {
      assert(pos[j] != 2);
      if (pos[j] == 0) n_AuB--;
    }

    int64_t a = N*N - 2*N + n_AuB;

    int64_t b_lb = 0;
    for (int j = 0; j < N; ++j) {
      if (j != 0) b_lb += n_AuB * x[j]->getMin();
      if (pos[j] == 0) b_lb += 2 * N * x[j]->getMin();
    }

    int64_t b_ub = 0;
    for (int j = 0; j < N; ++j) {
      if (j != 0) b_ub += n_AuB * x[j]->getMax();
      if (pos[j] == 0) b_ub += 2 * N * x[j]->getMax();
    }

    // explanation
    Clause *r = nullptr;
    if (so.lazy) {
      // Set up reason
      Lit lit[2 * N + 3];
      int lits = 0;

      // For using all x's ub's and lb's
      for(int ii = 0; ii < N; ++ii) {
        lit[lits++] = x[ii]->getMinLit();
        lit[lits++] = x[ii]->getMaxLit();
      }

      // For using VxU
      lit[lits++] = y->getMaxLit();

      // For using pos[], double-check if necessary
      lit[lits++] = s->getMinLit();
      lit[lits++] = s->getMaxLit();

      r = Reason_new(lits + 1);
      for (int ii = 0; ii < lits; ++ii) (*r)[ii + 1] = lit[ii];
    }

    for (int i = 0; i < N; i++) {
      // overlap

//      assert(false && "not implemented yet");

      if (pos[i] == 0) {
        if (!prop_x_v1_O(i)) return false;
      }
      else if (pos[i] == -1 or pos[i] == 1) {
        int64_t c_lb = 0;
        int64_t term1 = 0;
        int64_t term2 = 0;
        for (int j = 0; j < N; ++j) {
          if (j != 0) term1 += x[j]->getMin();
        }
        term1 *= term1;

        for (int j = 0; j < N; ++j) { // TODO: FIXME: ERRORS!
          if (pos[j] == 0) continue;

          int64_t sq = INT64_MAX;
          for (int jj = 0; (jj < 4) && (pos[j] == -1 || pos[j] == 1); jj++) {
            int64_t temp = 0;
            if (jj == 0 || jj == 1) temp = s->getMin();
            else                    temp = s->getMax();
            if (jj == 0 || jj == 2) temp = N * x[i]->getMax() - temp;
            else                    temp = N * x[i]->getMin() - temp;
            temp *= temp;
            if (temp < sq) sq = temp;
          }
          term2 += sq;
        }

        c_lb = term1 + term2;

        if (!prop_x_v1x_AB(i, n_AuB, a, b_lb, b_ub, c_lb, r)) return false;
      }
    }
    return true;
  }

  bool prop_x_v1_O(int i) {
    const int reset = std::fegetround();

    std::fesetround(FE_DOWNWARD);
    auto Lx = fmax((long double) (N*x[i]->getMin()),
                   (long double) s->getMin());
    std::fesetround(FE_UPWARD);
    auto VxU = floorl(
        (long double) ((int64_t) (y->getMax() + 1) * N * N * N) /
        (long double) scale);
    auto sqrtK = sqrtl(VxU - (long double) Vx);
    auto x_lb = (int64_t) ceil( (Lx - sqrtK ) / N);

    auto Ux = fmax((long double) (N*x[i]->getMax()),
                   (long double) s->getMax());
    std::fesetround(FE_DOWNWARD);
    auto x_ub = (int64_t) floor( (Ux + sqrtK) / N);

//    printf("%%\t Ux = %LF, VxU = %LF, sqrtK = %LF, x_ub = %d, yGetMax = %LF, scale = %LF, y->getMax() = %d, Vx = %lld, N = %d, y->getMin() = %d\n",
//        Ux, VxU, sqrtK, x_ub, (long double) ((int64_t) (y->getMax() + 1) * N * N * N), (long double) scale, y->getMax(), Vx.v, N, y->getMin());

    // explanation
    Clause *r = nullptr;
    if (x[i]->setMinNotR(x_lb) || x[i]->setMaxNotR(x_ub)) {
      n_prop_x_overlap++;
      if (so.lazy) {
        // Set up reason
        Lit lit[2 * N + 6];
        int lits = 0;

        // not needed
        for(int ii = 0; ii < N; ++ii) {
          //if (pos[ii] == 1)
            lit[lits++] = x[ii]->getMinLit();
          //else if (pos[ii] == -1)
            lit[lits++] = x[ii]->getMaxLit();
        }

        // For using Lx and Ux
        //if ((int64_t)Ux == N*x[i]->getMax())
        lit[lits++] = x[i]->getMaxLit();
        //else
        lit[lits++] = s->getMaxLit();
        //if ((int64_t)Lx == N*x[i]->getMin())
        lit[lits++] = x[i]->getMinLit();
        //else
        lit[lits++] = s->getMinLit();

        // For using Vx and VxU
        lit[lits++] = y->getMaxLit();
        lit[lits++] = y->getMinLit();
        r = Reason_new(lits + 1);
        for (int ii = 0; ii < lits; ++ii) (*r)[ii + 1] = lit[ii];
      }
    }

    // prune

    x_overlap_max_strength = lli_max(x_overlap_max_strength, x_lb - x[i]->getMin());
    if (x[i]->setMinNotR(x_lb)) {
      std::fesetround(reset);
      if (!x[i]->setMin(x_lb, r)) {
//        printf("%%\t lb false\n");
//        printf("%%\t lb is %d want to set to %d\n", x[i]->getMin(), x_lb);
        n_incons_x_overlap++;
        return false;
      }
    }
    x_overlap_max_strength = lli_max(x_overlap_max_strength, x[i]->getMax() - x_ub);
    if (x[i]->setMaxNotR(x_ub)) {
      std::fesetround(reset);
      if (!x[i]->setMax(x_ub, r)) {
//        printf("%%\t ub false\n");
//        printf("%%\t ub is %d want to set to %d\n", x[i]->getMax(), x_ub);
        n_incons_x_overlap++;
        return false;
      }
    }
    return true;
  }

  bool prop_x_v1_AB(int i) {
    assert(false && "TODO, not implemented yet");
  }

  //------------------//
  // Version 1 Approx // mode = 2
  //------------------//

  bool prop_x_v1x() {
    int n_AuB = N;
    for (int j = 0; j < N; j++) {
      assert(pos[j] != 2);
      if (pos[j] == 0) n_AuB--;
    }

    int64_t a = N*N - 2*N + n_AuB;

    int64_t b_lb = 0;
    for (int j = 0; j < N; ++j) {
      if (j != 0) b_lb += n_AuB * x[j]->getMin();
      if (pos[j] == 0) b_lb += 2 * N * x[j]->getMin();
    }

    int64_t b_ub = 0;
    for (int j = 0; j < N; ++j) {
      if (j != 0) b_ub += n_AuB * x[j]->getMax();
      if (pos[j] == 0) b_ub += 2 * N * x[j]->getMax();
    }

    int64_t c_lb = 0;
    int max_lb_x = 0;
    for (int j = 0; j < N; ++j) {
      if (x[j]->getMin() > max_lb_x) max_lb_x = x[j]->getMin();
      c_lb += x[j]->getMin();
    }
    c_lb -= max_lb_x;
    c_lb = c_lb * c_lb;

    // explanation
    Clause *r = nullptr;
    if (so.lazy) {
      // Set up reason
      Lit lit[2 * N + 3];
      int lits = 0;

      // For using all x's ub's and lb's
      for(int ii = 0; ii < N; ++ii) {
        lit[lits++] = x[ii]->getMinLit();
        lit[lits++] = x[ii]->getMaxLit();
      }

      // For using VxU
      lit[lits++] = y->getMaxLit();

      // For using pos[], double-check if necessary
      lit[lits++] = s->getMinLit();
      lit[lits++] = s->getMaxLit();

      r = Reason_new(lits + 1);
      for (int ii = 0; ii < lits; ++ii) (*r)[ii + 1] = lit[ii];
    }

    for (int i = 0; i < N; i++) {
      // overlap
      if (pos[i] == 0) {
        if (!prop_x_v1_O(i)) return false;
      }

      // above or below
      else {
        if (i > 0) {
          b_lb -= n_AuB * x[i]->getMin();
          b_lb += n_AuB * x[i-1]->getMin();
          b_ub -= n_AuB * x[i]->getMax();
          b_ub += n_AuB * x[i-1]->getMax();
        }
        if (!prop_x_v1x_AB(i, n_AuB, a, b_lb, b_ub, c_lb, r)) return false;
      }
    }
    return true;
  }

  bool prop_x_v1x_AB(int i, int n_AuB, int64_t a, int64_t b_lb, int64_t b_ub,
      int64_t c_lb, Clause *r) {
//    printf("%% running prop_x_v1x_AB\n");

    const int reset = std::fegetround();

    std::fesetround(FE_UPWARD);
    auto VxU = floorl(
        (long double) ((int64_t) (y->getMax() + 1) * N * N * N) /
        (long double) scale);
    auto sqrtExprL = sqrtl(4*a*VxU + 4*a*c_lb + b_ub*b_ub);
    auto sqrtExprU = sqrtl(4*a*VxU + 4*a*c_lb + b_ub*b_ub);

    std::fesetround(FE_DOWNWARD);
    auto x_lb = (int64_t) ceill( (-sqrtExprL - b_ub) / 2*a);

    std::fesetround(FE_UPWARD);
    auto x_ub = (int64_t) floorl( (sqrtExprU - b_lb) / 2*a);

//    cout << "\n%% x_lb's sqrtExprL = sqrtl(4*" << a << "*" << VxU << " + 4*" << a << "*" << c_lb << " + " << b_ub << "*" << b_ub << ")"
//         << "\n%% x_ub's sqrtExprU = sqrtl(4*" << a << "*" << VxU << " + 4*" << a << "*" << c_lb << " + " << b_ub << "*" << b_ub << ")"
//         << "\n%% x_lb = ceill( (-" << sqrtExprU << " - " << b_ub << " / 2*" << a << ")"
//         << "\n%% x_ub = floorl( (" << sqrtExprU << " - " << b_lb << " / 2*" << a << ")"
//         << endl
//         << "%% We try to propagate: "
//         << x_lb << " <= " << x[i]->getMin() << " <= X[" << i+1 << "] <= "
//         << x[i]->getMax() << " <= " << x_ub << "\n % \n %" << endl;

    // Strength
    if (pos[i] == -1) x_below_max_strength = lli_max(x_below_max_strength, x_lb - x[i]->getMin());
    if (pos[i] == -1) x_below_max_strength = lli_max(x_below_max_strength, x[i]->getMax() - x_ub);
    if (pos[i] == 0) x_overlap_max_strength = lli_max(x_overlap_max_strength, x_lb - x[i]->getMin());
    if (pos[i] == 0) x_overlap_max_strength = lli_max(x_overlap_max_strength, x[i]->getMax() - x_ub);
    if (pos[i] == 1) x_above_max_strength = lli_max(x_above_max_strength, x_lb - x[i]->getMin());
    if (pos[i] == 1) x_above_max_strength = lli_max(x_above_max_strength, x[i]->getMax() - x_ub);

    // Prune
    if (x[i]->setMinNotR(x_lb) || x[i]->setMaxNotR(x_ub)) {
      if (pos[i] == 1) { n_prop_x_above++; cout << "%% v1x_AB x_lb/ub prop\n"; }
      else if (pos[i] == -1) n_prop_x_below++;
      else if (pos[i] == 0) n_prop_x_overlap++;
    }

//    if (x_lb <= INT64_MIN) CHUFFED_ERROR("Spread constraint may underflow, not yet supported");
//    if (x_ub >= INT64_MAX) CHUFFED_ERROR("Spread constraint may overflow, not yet supported");

    if (x[i]->setMinNotR(x_lb)) {
      std::fesetround(reset);
      if (!x[i]->setMin(x_lb, r)) {
        cerr << "constraint (";

//        // For using all x's ub's and lb's
//        for(int ii = 0; ii < N; ++ii) {
//          cerr << "X[" << ii+1 << "] >= " << x[ii]->getMin()
//               << " /\\ "
//               << "X[" << ii+1 << "] <= " << x[ii]->getMax()
//               << " /\\ ";
//        }
//
//        // For using VxU
//        cerr << "v <= " << y->getMax();
//
//        // Not needed!?!?
//        cerr << " /\\ "
//             << "v >= " << y->getMin()
//             << " /\\ "
//             << "S >= " << s->getMin()
//             << " /\\ "
//             << "S <= " << s->getMax();
//
//        // Finish
//        cerr << ") -> ("
//             << "X[" << i+1 << "] >= " << x_lb
//             << "); % ";
//
//        for (int i = 0; i < N; ++i) {
//          cerr << "pos[X[" << i+1 << "]] = " << pos[0];
//        }
//
//        cerr << ", Vx = " << Vx.v
//             << ", VxU = " << VxU
//             << ", Mx = " << Mx.v
//             << ", MxR = " << MxR.v
//             << ", a = " << a
//             << ", b" << i << "_lb = " << b_lb
//             << ", b" << i << "_ub = " << b_ub
//             << ", c" << i << "_lb = " << c_lb
//             << endl;
//
        if (pos[i] == 1) { n_incons_x_above++;  cout << "%% v1x_AB x_lb FAIL\n"; }
        else if (pos[i] == -1) n_incons_x_below++;
        else if (pos[i] == 0) n_incons_x_overlap++;
        return false;
      }
    }
    if (x[i]->setMaxNotR(x_ub)) {
      std::fesetround(reset);
//      if (pos[i] == 1) { n_prop_x_above++;  cout << "%% v1x_AB x_ub prop\n"; }
//      else if (pos[i] == -1) n_prop_x_below++;
//      else if (pos[i] == 0) n_prop_x_overlap++;
      if (!x[i]->setMax(x_ub, r)) {
        cerr << "constraint (";

        // For using all x's ub's and lb's
        for(int ii = 0; ii < N; ++ii) {
          cerr << "X[" << ii+1 << "] >= " << x[ii]->getMin()
               << " /\\ "
               << "X[" << ii+1 << "] <= " << x[ii]->getMax()
               << " /\\ ";
        }

        // For using VxU
        cerr << "v <= " << y->getMax();

        // Not needed!?!?
        cerr << " /\\ "
             << "v >= " << y->getMin()
             << " /\\ "
             << "S >= " << s->getMin()
             << " /\\ "
             << "S <= " << s->getMax();

        // Finish
        cerr << ") -> ("
             << "X[" << i+1 << "] >= " << x_lb
             << "); % ";

        for (int i = 0; i < N; ++i) {
          cerr << "pos[X[" << i+1 << "]] = " << pos[0];
        }

        cerr << ", Vx = " << Vx.v
             << ", VxU = " << VxU
             << ", Mx = " << Mx.v
             << ", MxR = " << MxR.v
             << ", a = " << a
             << ", b" << i << "_lb = " << b_lb
             << ", b" << i << "_ub = " << b_ub
             << ", c" << i << "_lb = " << c_lb
             << endl;

        if (pos[i] == 1) { n_incons_x_above++; cout << "%% v1x_AB x_ub FAIL\n"; }
        else if (pos[i] == -1) n_incons_x_below++;
        else if (pos[i] == 0) n_incons_x_overlap++;
        return false;
      }
    }
    return true;
  }

  //-----------//
  // Version 2 // mode = 3
  //-----------//

  bool prop_x_v2() {
    int64_t a = N*N - N;

    int64_t b_lb = 0;
    for (int j = 1; j < N; ++j) {
      if (N > 2) b_lb += (2 - N) * x[j]->getMax();
      else if (N < 2) b_lb += (2 - N) * x[j]->getMin();
    }

    int64_t b_ub = 0;
    for (int j = 1; j < N; ++j) {
      if (N > 2) b_ub += (2 - N) * x[j]->getMin();
      else if (N < 2) b_ub += (2 - N) * x[j]->getMax();
    }

    // explanation
    Clause *r = nullptr;
    if (so.lazy) {
      // Set up reason
      Lit lit[2 * N + 3];
      int lits = 0;

      // For using all x's ub's and lb's
      for(int ii = 0; ii < N; ++ii) {
        lit[lits++] = x[ii]->getMinLit();
        lit[lits++] = x[ii]->getMaxLit();
      }

      // For using VxU
      lit[lits++] = y->getMaxLit();

      // For using pos[], double-check if necessary
      lit[lits++] = s->getMinLit();
      lit[lits++] = s->getMaxLit();

      r = Reason_new(lits + 1);
      for (int ii = 0; ii < lits; ++ii) (*r)[ii + 1] = lit[ii];
    }

    for (int i = 0; i < N; i++) {
      if (i > 0) {
        if (N > 2) {
          b_lb -= (2 - N) * x[i]->getMax();
          b_lb += (2 - N) * x[i-1]->getMax();
          b_ub -= (2 - N) * x[i]->getMin();
          b_ub += (2 - N) * x[i-1]->getMin();
        }
        else if (N < 2) {
          b_lb -= (2 - N) * x[i]->getMin();
          b_lb += (2 - N) * x[i-1]->getMin();
          b_ub -= (2 - N) * x[i]->getMax();
          b_ub += (2 - N) * x[i-1]->getMax();
        }
      }
      int64_t c_lb = 0;
      int64_t term1 = 0;
      int64_t term2 = 0;
      for (int j = 0; j < N; ++j) {
        if (j != 0) term1 += x[j]->getMin();
      }
      term1 *= term1;

//      for (int j = 0; j < N; ++j) {
//        if (i == j) continue;
//
//        int64_t sq = INT64_MAX;
//        for (int jj = 0; jj < 4; jj++) {
//          int64_t temp = 0;
//          if (jj == 0 || jj == 1) temp = s->getMin() - x[i]->getMin();
//          else                    temp = s->getMax() - x[i]->getMax();
//          if (jj == 0 || jj == 2) temp = N * x[j]->getMax() - temp;
//          else                    temp = N * x[j]->getMin() - temp;
//          temp *= temp;
//          if (temp < sq) sq = temp;
//        }
//        term2 += sq;
//      }

//      cout << "% next: var for " << i << " of " << N-1 <<  endl;
      for (int64_t sum = s->getMin() - x[i]->getMin();
             sum <= s->getMax() - x[i]->getMax(); ++sum) {
//        cout << "sum = " << sum << endl;
        int64_t temp = 0;
        for (int ii = 0; ii < N; ++ii) {
          if (i == ii) continue;
          int64_t lb = N * x[ii]->getMin(), ub = N * x[ii]->getMax();
          if (sum < lb)      temp += (lb - sum) * (lb - sum);
          else if (ub < sum) temp += (ub - sum) * (ub - sum);
        }
        if (temp < term2) term2 = temp;
      }
//      cout << "% var done for " << i << " of " << N-1 << endl;

      c_lb = term1 + term2;

      if (!prop_x_v1x_AB(i, 0, a, b_lb, b_ub, c_lb, r)) return false;
//      cout << "% prop_x_v1x_AB done for " << i << " of " << N-1 << endl;
    }
    return true;
  }

  //------------------//
  // Version 2 Approx // mode = 4
  //------------------//

  bool prop_x_v2x(){
    int64_t a = N*N - N;

    int64_t b_lb = 0;
    for (int j = 1; j < N; ++j) {
      if (N > 2) b_lb += (2 - N) * x[j]->getMax();
      else if (N < 2) b_lb += (2 - N) * x[j]->getMin();
    }

    int64_t b_ub = 0;
    for (int j = 1; j < N; ++j) {
      if (N > 2) b_ub += (2 - N) * x[j]->getMin();
      else if (N < 2) b_ub += (2 - N) * x[j]->getMax();
    }

    int64_t c_lb = 0;
    int max_lb_x = 0;
    for (int j = 0; j < N; ++j) {
      if (x[j]->getMin() > max_lb_x) max_lb_x = x[j]->getMin();
      c_lb += x[j]->getMin();
    }
    c_lb -= max_lb_x;
    c_lb = c_lb * c_lb;

    // explanation
    Clause *r = nullptr;
    if (so.lazy) {
      // Set up reason
      Lit lit[2 * N + 3];
      int lits = 0;

      // For using all x's ub's and lb's
      for(int ii = 0; ii < N; ++ii) {
        lit[lits++] = x[ii]->getMinLit();
        lit[lits++] = x[ii]->getMaxLit();
      }

      // For using VxU
      lit[lits++] = y->getMaxLit();

      // For using pos[], double-check if necessary
      lit[lits++] = s->getMinLit();
      lit[lits++] = s->getMaxLit();

      r = Reason_new(lits + 1);
      for (int ii = 0; ii < lits; ++ii) (*r)[ii + 1] = lit[ii];
    }

    for (int i = 0; i < N; i++) {
      if (i > 0) {
        if (N > 2) {
          b_lb -= (2 - N) * x[i]->getMax();
          b_lb += (2 - N) * x[i-1]->getMax();
          b_ub -= (2 - N) * x[i]->getMin();
          b_ub += (2 - N) * x[i-1]->getMin();
        }
        else if (N < 2) {
          b_lb -= (2 - N) * x[i]->getMin();
          b_lb += (2 - N) * x[i-1]->getMin();
          b_ub -= (2 - N) * x[i]->getMax();
          b_ub += (2 - N) * x[i-1]->getMax();
        }
      }
      if (!prop_x_v1x_AB(i, 0, a, b_lb, b_ub, c_lb, r)) return false;
    }
    return true;
  }

  //------------//
  // DC Version // mode = 6
  //------------//

  void init_dc() {
    pos.growTo(N);
    for (int i = 0; i < N; ++i) pos[i] = 2;
    for (int i = 0; i < N; i++) {
      x[i]->attach(this, i, EVENT_C);
    }
    y->attach(this, N, EVENT_C);
    s->attach(this, N+1, EVENT_LU);

    int n_fixed_ = 0;
    for (int i = 0; i < N; ++i) {
      if (x[i]->isFixed()) n_fixed_++;
    }
    n_fixed = n_fixed_;
  }

  bool prop_x_dc(){
//    cout << "dc:\n\tinit" << endl;

    // Initialize
    vec<vec<bool> > support;
    vec<vec<int64_t> > val;
    vec<int64_t> idx;
    for (int i = 0; i <= N; ++i) {
      support.push(vec<bool>());
      val.push(vec<int64_t>());
      idx.push(0);
      int64_t vlb = (i < N) ? x[i]->getMin() : y->getMin();
      int64_t vub = (i < N) ? x[i]->getMax() : y->getMax();
      for (int64_t ii = 0; ii + vlb <= vub; ++ii) {
        support[i].push(false);
        val[i].push(vlb + ii);
      }
    }

//    cout << "\ttry all comb" << endl;
    // Try all combinations
    bool not_done = true;
    while (not_done) {

      // Try combination
      int64_t sumx = 0;
      for (int i = 0; i < N; i++) sumx += val[i][idx[i]];

      int64_t sqdiff = 0;
      for (int i = 0; i < N; i++) {
        int64_t diff = N * val[i][idx[i]] - sumx;
        sqdiff += diff * diff;
      }

      long double result_f = (long double) sqdiff / (long double) (N*N*N);
      int64_t result = (int64_t) (result_f * scale);

      if (result == val[N][idx[N]]) {
        for (int i = 0; i <= N; ++i) {
          support[i][idx[i]] = true;
        }
      }

      // Increment to next combination
      for (int i = 0; i <= N; ++i) {
        if (i == N && val[i][idx[i]] == y->getMax()) {
          not_done = false;
          break;
        } else if (i != N && val[i][idx[i]] == x[i]->getMax()) {
          idx[i] = 0;
        } else {
          ++idx[i];
          break;
        }
      }
    }

//    cout << "\tfull expl" << endl;
    // Full explanation
    Clause *r = nullptr;
    if (so.lazy) {
      vec<Lit> lits;

      // All-encompassing reason
      for (int i = 0; i < N; ++i) {
        lits.push(x[i]->getMinLit());
        lits.push(x[i]->getMaxLit());
        for (int64_t val = x[i]->getMin()+1; val < x[i]->getMax(); ++val) {
          if(!x[i]->indomain(val)) lits.push(*x[i] != val);
        }
      }
      lits.push(y->getMinLit());
      lits.push(y->getMaxLit());
      for (int64_t val = y->getMin()+1; val < y->getMax(); ++val) {
        if(!y->indomain(val)) lits.push(*y != val);
      }

      r = Reason_new(lits);
    }

//    cout << "\trem combs" << endl;
    // Remove combinations
    for (int i = 0; i < N; ++i) {
      bool did = false;
      for (int64_t ii = 0; ii + x[i]->getMin() <= x[i]->getMax(); ++ii) {
        if (support[i][ii]) continue;
        if (x[i]->remValNotR(val[i][ii])) {
          // --> TEST PRINT
          if (!did) {
            did = true;
            cout << "%%% Propagates: Domains: ";
            for (int ii = 0; ii < N; ++ii) {
              int64_t dom_len, dom_size = 0;
              dom_len = x[ii]->getMax() - x[ii]->getMin() + 1;
              for (int64_t v = x[ii]->getMin(); v <= x[ii]->getMax(); ++v) {
                if (x[ii]->indomain(v)) ++dom_size;
              }
              cout << dom_len << " (" << dom_size << "), ";
            }
            int64_t dom_len, dom_size = 0;
            dom_len = y->getMax() - y->getMin() + 1;
            for (int64_t v = y->getMin(); v <= y->getMax(); ++v) {
              if (y->indomain(v)) ++dom_size;
            }
            cout << dom_len << " (" << dom_size << ")" << endl;
          }
          // <-- END TEST PRINT
          n_prop_x++;
          if (!x[i]->remVal(val[i][ii], r)) {
            n_incons_x++;
            return false;
          }
        }
      }
    }
    bool did = false;
    for (int64_t ii = 0; ii + y->getMin() <= y->getMax(); ++ii) {
      if (support[N][ii]) continue;
      if (y->remValNotR(val[N][ii])) {
        // --> TEST PRINT
        if (!did) {
          did = true;
          cout << "%%% VAR Propagates: Domains: ";
          for (int ii = 0; ii < N; ++ii) {
            int64_t dom_len, dom_size = 0;
            dom_len = x[ii]->getMax() - x[ii]->getMin() + 1;
            for (int64_t v = x[ii]->getMin(); v <= x[ii]->getMax(); ++v) {
              if (x[ii]->indomain(v)) ++dom_size;
            }
            cout << dom_len << " (" << dom_size << "), ";
          }
          int64_t dom_len, dom_size = 0;
          dom_len = y->getMax() - y->getMin() + 1;
          for (int64_t v = y->getMin(); v <= y->getMax(); ++v) {
            if (y->indomain(v)) ++dom_size;
          }
          cout << dom_len << " (" << dom_size << ")" << endl;
        }
        // <-- END TEST PRINT
        n_prop_v++;
        if (!y->remVal(val[N][ii], r)) {
          n_incons_v++;
          return false;
        }
      }
    }

//    cout << "\tsuccess, return" << endl;
    // Success
    return true;
  }

  //------------//
  // Smart Mode // mode = 7
  //------------//

  bool prop_x_v7() {
    bool one_fixed_ = y->isFixed();
    for (int i = 0; i < N && !one_fixed; ++i) {
      one_fixed_ = x[i]->isFixed();
    }
    one_fixed = one_fixed_;
    for (int i = 0; i < N; i++) {
      if (pos[i] == 0) {
        if (!prop_x_v1_O(i)) return false;
      }
    }
    if (one_fixed) {
      if (!prop_x_v2()) return false;
    }
    return true;
  }

  //--------//
  // New LB // mode = 8
  //--------//

  bool prop_var_lb_new() {
    int64_t L = s->getMin();
    int64_t R = s->getMax();
    int64_t V = 0;
    int64_t M = 0;
    while (L < R) {
      int64_t mid_L = L + (R - L)/2;
      int64_t mid_R = mid_L + 1;

      int64_t V_L = 0, V_R = 0, M_L = 0, M_R = 0, Sq_L = 0, Sq_R = 0;
      for (int i = 0; i < N; ++i) {
        int64_t xlb = N*x[i]->getMin();
        int64_t xub = N*x[i]->getMax();

        if      (xub <= mid_L) {M_L += xub; Sq_L += xub*xub;} // below mid_L
        else if (mid_L <= xlb) {M_L += xlb; Sq_L += xlb*xlb;} // above mid_L
        else {M_L += mid_L; Sq_L += mid_L*mid_L;} // overlap mid_L

        if      (xub <= mid_R) {M_R += xub; Sq_R += xub*xub;} // below mid_R
        else if (mid_R <= xlb) {M_R += xlb; Sq_R += xlb*xlb;} // above mid_R
        else {M_R += mid_R; Sq_R += mid_R*mid_R;} // overlap mid_R
      }

      V_L = N*Sq_L - M_L*M_L;
      V_R = N*Sq_R - M_R*M_R;

//      printf("%% PRE LB Prop %%, (V_L at mid_L, V_R at mid_R) = (%lli at %lli, %lli at %lli)\n", V_L, mid_L, V_R, mid_R);
//      printf("  %% Sq_L=%lli, Sq_R=%lli, M_L=%lli, M_R=%lli\n", Sq_L, Sq_R, M_L, M_R);

      if (V_L == 0 || V_R == 0) {return true;} // worst lb found
      if (V_L == V_R) {V = V_L; M = mid_L; break;} // found lb
      if      (V_L < V_R) {V = V_L; M = mid_L; R = mid_L;} // search left
      else if (V_L > V_R) {V = V_R; M = mid_R; L = mid_R;} // search right
    }

    // update positions
    for (int i = 0; i < N; ++i) { // O(N)
      if      (M < N*x[i]->getMin()) pos[i] =  1;
      else if (N*x[i]->getMax() < M) pos[i] = -1;
      else                           pos[i] =  0;
    }

    // get scaled variance
    const int reset = std::fegetround();
    std::fesetround(FE_DOWNWARD);
    auto scaled_var = (int64_t) (((long double) (V * scale)) / (N*N*N*N));
    std::fesetround(reset);

    if (y->setMinNotR(scaled_var)) {
      n_prop_v_lb++;
      Clause* r = nullptr;
      if(so.lazy) {
        Lit lit[N+2];
        int lits = 0;
        for(int ii = 0; ii < N; ++ii) {
          if      (pos[ii] ==  1) lit[lits++] = x[ii]->getMinLit();
          else if (pos[ii] == -1) lit[lits++] = x[ii]->getMaxLit();
          //else if (pos[ii] ==  0) {
          //  lit[lits++] = x[ii]->getMinLit();
          //  lit[lits++] = x[ii]->getMaxLit();
          //}
        }
        if (M == s->getMin()) lit[lits++] = s->getMinLit();
        if (M == s->getMax()) lit[lits++] = s->getMaxLit();

        // lit[lits++] = y->getMinLit();
        // lit[lits++] = y->getMaxLit();
        r = Reason_new(lits+1);
        for(int ii = 0; ii < lits; ++ii) (*r)[ii+1] = lit[ii];
      }
//      if (scaled_var >= INT64_MAX)
//      printf("%% LB Prop %%\n");
//      for (int i = 0; i < N; ++i) printf("   %% x[%d] = %d..%d      ", i, x[i]->getMin(), x[i]->getMax());
//      printf("%% y = %d..%d      ", y->getMin(), y->getMax());
//      printf("%% s = %d..%d\n", s->getMin(), s->getMax());
//      printf("   %% want to set y to %lli when it is %d..%d\n", scaled_var, y->getMin(), y->getMax());
      if(!y->setMin(scaled_var, r)) {
        n_incons_v_lb++;
        return false;
      }
    }
    return true;
  }

  //---------//
  // Best LB // mode = 9
  //---------//

  bool prop_var_lb_real() {
    int64_t L = s->getMin();
    int64_t R = s->getMax();
    int64_t V = 0;
    int64_t M = 0;
    while (L < R) {
      int64_t mid_L = L + (R - L)/2;
      int64_t mid_R = mid_L + 1;

      int64_t V_L = 0, V_R = 0;
      for (int i = 0; i < N; ++i) {
        int64_t xlb = N*x[i]->getMin();
        int64_t xub = N*x[i]->getMax();

        if      (xub <= mid_L) {V_L += (xub - mid_L)*(xub - mid_L);} // below mid_L
        else if (mid_L <= xlb) {V_L += (xlb - mid_L)*(xlb - mid_L);} // above mid_L
        else {} // overlap mid_L

        if      (xub <= mid_R) {V_R += (xub - mid_R)*(xub - mid_R);} // below mid_R
        else if (mid_R <= xlb) {V_R += (xlb - mid_R)*(xlb - mid_R);} // above mid_R
        else {} // overlap mid_R
      }

//      printf("%% PRE LB Prop %%\n");
//      printf("  %% (L, R) = (%d, %d)\n", L, R);
//      printf("  %% (V_L at mid_L, V_R at mid_R) = (%lli at %lli, %lli at %lli)\n", V_L, mid_L, V_R, mid_R);
//      printf("  %% Prev (V, M) = (%d, %d)\n", V, M);
      //printf("  %% Sq_L=%lli, Sq_R=%lli, M_L=%lli, M_R=%lli\n", Sq_L, Sq_R, M_L, M_R);

      if (V_L == 0 || V_R == 0) {return true;} // worst lb found
      if (V_L == V_R) {V = V_L; M = mid_L; break;} // found lb
      if      (V_L < V_R) {V = V_L; M = mid_L; R = mid_L;} // search left
      else if (V_L > V_R) {V = V_R; M = mid_R; L = mid_R;} // search right
    }

    // update positions
    for (int i = 0; i < N; ++i) { // O(N)
      if      (M < N*x[i]->getMin()) pos[i] =  1;
      else if (N*x[i]->getMax() < M) pos[i] = -1;
      else                           pos[i] =  0;
    }

    // get scaled variance
    const int reset = std::fegetround();
    std::fesetround(FE_DOWNWARD);
    auto scaled_var = (int64_t) (((long double) (V * scale)) / (N*N*N));
    std::fesetround(reset);

    //printf("%% outside\n");
    if (y->setMinNotR(scaled_var)) {
      //printf("%% ..inside\n");
      n_prop_v_lb++;
      Clause* r = nullptr;
      if(so.lazy) {
        Lit lit[2*N+2];
        int lits = 0;
//        printf("constraint (");
        for(int ii = 0; ii < N; ++ii) {
          if      (pos[ii] ==  1) {
            lit[lits++] = x[ii]->getMinLit();
//            printf(" util[%d] >= %d /\\ ", ii+1, x[ii]->getMin());
          }
          else if (pos[ii] == -1) {
            lit[lits++] = x[ii]->getMaxLit();
//            printf(" util[%d] <= %d /\\ ", ii+1, x[ii]->getMax());
          }
          //else if (pos[ii] ==  0) {
          //  lit[lits++] = x[ii]->getMinLit();
          //  lit[lits++] = x[ii]->getMaxLit();
          //}
        }
        if (M == s->getMin()) {
          lit[lits++] = s->getMinLit();
//          printf(" UTIL <= %d /\\ ", s->getMax());
        }
        if (M == s->getMax()) {
          lit[lits++] = s->getMaxLit();
//          printf(" UTIL <= %d /\\ ", s->getMax());
        }

//        printf(" true) -> ( disp >= %d (actually %lli) ); %% EXPL\n", scaled_var, scaled_var);

        // lit[lits++] = y->getMinLit();
        // lit[lits++] = y->getMaxLit();
        r = Reason_new(lits+1);
        for(int ii = 0; ii < lits; ++ii) (*r)[ii+1] = lit[ii];
      }
//      if (scaled_var >= INT64_MAX)
//      if (x[1]->getMin() == 3192 && x[2]->getMin() == 3041 && scaled_var == 1428) {
//        printf("%% LB Prop %%\n");
//        for (int i = 0; i < N; ++i) printf("   %% x[%d] = %d..%d      ", i, x[i]->getMin(), x[i]->getMax());
//        printf("%% y = %d..%d      ", y->getMin(), y->getMax());
//        printf("%% s = %d..%d\n", s->getMin(), s->getMax());
//        printf("   %% want to set y to %lli when it is %d..%d\n", scaled_var, y->getMin(), y->getMax());
//      }
      if(!y->setMin(scaled_var, r)) {
        n_incons_v_lb++;
        return false;
      }
    }
    return true;
  }

  //-----------//
  // OLD STUFF //
  //-----------//

  bool prop_x() {

    // TODO only perfect precision when N*N*N < scale, perhaps okay for rough precision.
    const int reset = std::fegetround();
    std::fesetround(FE_UPWARD);
    auto n3var_upr = (int64_t) floorl(
        (long double) ((y->getMax() + 1) * N * N * N) /
        (long double) scale);

    int64_t min_sum = s->getMin(), max_sum = s->getMax();
    int64_t min_sum_b = 0, max_sum_b = 0;
    for (int i = 0; i < N; ++i) {
      min_sum_b += x[i]->getMin();
      max_sum_b += x[i]->getMax();
    }


    if (mode == 2) {
      // propagate x's
      int64_t mins[N];
      int64_t min_var_sum = 0;
      for (int i = 0; i < N; ++i) { // O(N)
        int64_t xlb = x[i]->getMin();
        int64_t xub = x[i]->getMax();
        int64_t Sub = max_sum_b - xub + xlb;
        int64_t Slb = min_sum_b - xlb + xub;
        if (Sub < N * xlb) { // above
          int64_t diff = N * xlb - Sub;
          mins[i] = (diff) * (diff);
          min_var_sum += mins[i];
        } else if (N * xub < Slb) { //below
          int64_t diff = N * xub - Slb;
          mins[i] = (diff) * (diff);
          min_var_sum += mins[i];
        } else { //overlap
          mins[i] = 0;
        }
      }

      for (int i = 0; i < N; ++i) { // O(N)
        int64_t remvar = min_var_sum - mins[i];
        int64_t xlb = x[i]->getMin();
        int64_t xub = x[i]->getMax();
        int64_t Sub = max_sum_b - xub + xlb;
        short above = Sub < N * xlb;
        int64_t Slb = min_sum_b - xlb + xub;
        short below = N * xub < Slb;
        std::fesetround(FE_UPWARD);
        long double sqrt = sqrtl(n3var_upr - remvar);
        if (above) {
          int64_t cand = max_sum;
          if (abs(N * xub - max_sum) > abs(N * xub - Slb)) cand = min_sum;
          std::fesetround(FE_UPWARD);
          long double div = (cand + sqrt) / N;
          auto upr = (int64_t) floorl(div);
          if (n3var_upr < remvar) upr = x[i]->getMin() - 1;
          if (x[i]->setMaxNotR(upr)) {
            Clause *r = nullptr;
            if (so.lazy) {
              // Set up reason
              Lit lit[2 * N + 2 + 2];
              int lits = 0;
              for (int ii = 0; ii < N; ++ii) {
                if (ii == i) continue;
                lit[lits++] = x[ii]->getMinLit();
                lit[lits++] = x[ii]->getMaxLit();
              }
              lit[lits++] = s->getMinLit();
              lit[lits++] = s->getMaxLit();
              lit[lits++] = y->getMaxLit();
              r = Reason_new(lits + 1);
              for (int ii = 0; ii < lits; ++ii) (*r)[ii + 1] = lit[ii];
            }
            std::fesetround(reset);
            if (!x[i]->setMax(upr, r)) return false;
          }
        }
        if (below) {
          int64_t cand = min_sum;
          //if (abs(N*xlb - min_sum) > abs(N*xlb - max_sum)) cand = max_sum;
          std::fesetround(FE_DOWNWARD);
          long double div = (cand - sqrt) / N;
          auto lwr = (int64_t) ceill(div);
          if (n3var_upr < remvar) lwr = x[i]->getMax() + 1;
          if (x[i]->setMinNotR(lwr)) {
            Clause *r = nullptr;
            if (so.lazy) {
              // Set up reason
              Lit lit[2 * N + 2];
              int lits = 0;
              for (int ii = 0; ii < N; ++ii) {
                if (ii == i) continue;
                lit[lits++] = x[ii]->getMinLit();
                lit[lits++] = x[ii]->getMaxLit();
              }
              lit[lits++] = s->getMinLit();
              lit[lits++] = s->getMaxLit();
              lit[lits++] = y->getMaxLit();
              r = Reason_new(lits + 1);
              for (int ii = 0; ii < lits; ++ii) (*r)[ii + 1] = lit[ii];
            }
            std::fesetround(reset);
            if (!x[i]->setMin(lwr, r)) return false;
          }
        }
      }
    } else { // mode is 3
      int64_t n3s = n3var_upr - Vx;
      for(int i = 0; i < N; ++i) {
        int64_t xub = x[i]->getMax();
        int64_t xlb = x[i]->getMin();

        int64_t Sub = max_sum_b - xub + xlb;
        int64_t Slb = min_sum_b - xlb + xub;

//        if (Mx.v != MxR.v){
//          printf("%% Mx = %lli, MxR = %lli\n", Mx.v, MxR.v);
//        }

        //overlap M
        if (pos[i] == 0) { // TODO: Why Mx.v here but not elsewhere?
          std::fesetround(FE_UPWARD);
          long double sqrt = sqrtl(n3s);

          int64_t Mxlb = s->getMin();
          if (Mxlb < N*xlb) Mxlb = N*xlb;
          std::fesetround(FE_DOWNWARD);
          auto n_xlb = (int64_t) ceill((Mxlb - sqrt) / N );

          int64_t Mxub = s->getMax();
          if (N*xub < Mxub) Mxub = N*xub;
          std::fesetround(FE_UPWARD);
          auto n_xub = (int64_t) floorl((Mxub + sqrt) / N );

          // explanation
          Clause *r = nullptr;
          if (x[i]->setMinNotR(n_xlb) || x[i]->setMaxNotR(n_xub)) {
            if (so.lazy) {
              // Set up reason
              Lit lit[2 * N + 4];
              int lits = 0;
              for (int ii = 0; ii < N; ++ii) {
//                if (ii == i) continue; // TODO: correct to ignore x[i] in expl?
                lit[lits++] = x[ii]->getMinLit();
                lit[lits++] = x[ii]->getMaxLit();
              }
              lit[lits++] = s->getMinLit();
              lit[lits++] = s->getMaxLit();
              lit[lits++] = y->getMaxLit();
              lit[lits++] = y->getMinLit();
              r = Reason_new(lits + 1);
              for (int ii = 0; ii < lits; ++ii) (*r)[ii + 1] = lit[ii];
            }
          }

          // prune
          if (x[i]->setMinNotR(n_xlb)) {
            std::fesetround(reset);
            if (!x[i]->setMin(n_xlb, r)) return false;
          }
          if (x[i]->setMaxNotR(n_xub)) {
            std::fesetround(reset);
            if (!x[i]->setMax(n_xub, r)) return false;
          }
        }

        //above M
        else if (pos[i] == 1 && (Mx.v == MxR.v)) {
          int64_t sq = (N*xub - Mx);
          sq = sq * sq;
          std::fesetround(FE_UPWARD);
          long double sqrt = sqrtl(n3s + sq);
          auto n_xub = (int64_t) floorl((Mx + sqrt) / N );

          // explanation
          Clause *r = nullptr;
          if (x[i]->setMaxNotR(n_xub)) {
            if (so.lazy) {
              //printf("constraint if ");
              // Set up reason
              Lit lit[2 * N + 4];
              int lits = 0;
              for (int ii = 0; ii < N; ++ii) {
                lit[lits++] = x[ii]->getMinLit();
//                if (ii != i) lit[lits++] = x[ii]->getMaxLit();
                lit[lits++] = x[ii]->getMaxLit();
//                printf("x[%d] <= %d /\\ ", ii, x[ii]->getMax());
//                printf("x[%d] >= %d /\\ ", ii, x[ii]->getMin());
              }
              lit[lits++] = s->getMinLit();
              lit[lits++] = s->getMaxLit();
              lit[lits++] = y->getMaxLit();
              lit[lits++] = y->getMinLit();
//              printf("s <= %d /\\ ", s->getMax());
//              printf("s >= %d /\\ ", s->getMin());
//              printf("variance <= %d /\\ ", y->getMax());
//              printf("variance >= %d", y->getMin());
//              printf(" then x[%d] <= %lli endif; /* SATCHEC */ \n", i, n_xub);

              r = Reason_new(lits + 1);
              for (int ii = 0; ii < lits; ++ii) (*r)[ii + 1] = lit[ii];
            }
          }

          // prune
          if (x[i]->setMaxNotR(n_xub)) {
            std::fesetround(reset);
//            printf("COUNTZ %lli\n", ++counter_prop);
//            printf("===\n");
//            for (int i = 0; i < N; ++i) printf("   %% x[%d] = %d..%d      ", i, x[i]->getMin(), x[i]->getMax());
//            printf("%% y = %d..%d      ", y->getMin(), y->getMax());
//            printf("%% s = %d..%d\n", s->getMin(), s->getMax());
//            printf("%% Mx = %lld and sq = %lli and sqrt = %Lf and n_xub = %lld and Vx = %lli and n3var_upr = %lli and n3s = %lli", Mx.v, sq, sqrt, n_xub, Vx.v, n3var_upr, n3s);
//            printf("   %% want to set x[%d] to %d..>%lli< when it is %d..%d\n", i, x[i]->getMin(), n_xub, x[i]->getMin(), x[i]->getMax());
            if (!x[i]->setMax(n_xub, r)) return false;
          }
        }
        //below M
        else if (pos[i] == -1 && (Mx.v == MxR.v)) {
          int64_t sq = (N*xlb - Mx);
          sq = sq * sq;
          std::fesetround(FE_DOWNWARD);
          long double sqrt = sqrtl(n3s + sq);
          auto n_xlb = (int64_t) ceill((Mx - sqrt) / N );

          // explanation
          Clause *r = nullptr;
          if (x[i]->setMinNotR(n_xlb)) {
            if (so.lazy) {
              // Set up reason
              Lit lit[2 * N + 4];
              int lits = 0;
              for (int ii = 0; ii < N; ++ii) {
//                if (ii != i) lit[lits++] = x[ii]->getMinLit();
                lit[lits++] = x[ii]->getMinLit();
                lit[lits++] = x[ii]->getMaxLit();
              }
              lit[lits++] = s->getMinLit();
              lit[lits++] = s->getMaxLit();
              lit[lits++] = y->getMaxLit();
              lit[lits++] = y->getMinLit();
              r = Reason_new(lits + 1);
              for (int ii = 0; ii < lits; ++ii) (*r)[ii + 1] = lit[ii];
            }
          }

          // prune
          if (x[i]->setMinNotR(n_xlb)) {
//            printf("COUNTZ %lli\n", ++counter_prop);
            std::fesetround(reset);
            if (!x[i]->setMin(n_xlb, r)) return false;
          }
        }
//        if pos[i] != -1,0,1 then do nothing
      }
    }
    std::fesetround(reset);
    return true;
  }

//  bool naive_prop() {
//    // mean
//    int64_t sumx_ub = 0;
//    for (int i = 0; i < N; i++) sumx_ub += x[i]->getMax();
//    long double mean_ub = (long double) sumx_ub / (long double) N;
//
//    int64_t sumx_lb = 0;
//    for (int i = 0; i < N; i++) sumx_lb += x[i]->getMin();
//    long double mean_lb = (long double) sumx_lb / (long double) N;
//
//    // squared diff
//    long double sqdiff_ub = 0;
//    for (int i = 0; i < N; i++) {
//      long double diff = (long double) x[i]->getMin() - mean_ub;
//      sqdiff += diff * diff;
//    }
//
//    // result
//    long double result_f = sqdiff / (long double) N;
//    uint64_t result = (int64_t) (result_f * scale);
//
//    //printf("%% sqdiff = %Lf and result = %lld", sqdiff, result);
//
//    // set y
//    if(y->setValNotR(result)) {
//      Clause* r = nullptr;
//      if(so.lazy) {
//        // Set up reason
//        r = Reason_new(N+1);
//        for(int ii = 0; ii < N; ++ii) { (*r)[ii+1] = x[ii]->getValLit(); }
//      }
//      if(!y->setVal(result, r)) return false;
//    }
//    return true;
//  }

  bool prop_var_ub() {
    // Popoviciu's inequality on variances
    int64_t min_lb = INT64_MAX;
    int64_t max_ub = INT64_MIN;
    for (int i = 0; i < N; i++) {
      int64_t lb = x[i]->getMin();
      int64_t ub = x[i]->getMax();
      if (lb < min_lb) {
        min_lb = lb;
        lb_idx = i;
      }
      if (ub > max_ub) {
        max_ub = ub;
        ub_idx = i;
      }
    }
    int64_t sqdiff = (max_ub - min_lb) * (max_ub - min_lb);
    long double var_ub_f = (long double) sqdiff / (long double) 4;
    int64_t var_ub = (int64_t) (var_ub_f * scale);

    // set y
    if(y->setMaxNotR(var_ub)) {
      Clause* r = nullptr;
      if(so.lazy) {
        // Set up reason
        r = Reason_new(2*N+1);
        for(int ii = 0; ii < N; ++ii) {
          (*r)[ii+1] = x[ii]->getMaxLit();
          (*r)[N+ii+1] = x[ii]->getMinLit();
        }
      }
      if(!y->setMax(var_ub, r)) return false;
    }
    return true;
  }
};

class CVInt : public Propagator {
public:
  int const N;
  IntVar *y;
  vec<IntVar*> x;
  IntVar *s;
  int scale;
  int mode;

  Tint subsumed;

  CVInt(IntVar *_y, vec<IntVar*> &_x, IntVar *_s, int _scale, int _mode) :
  N(_x.size()), y(_y), x(_x), scale(_scale), mode(_mode) {
    priority = 2;
    subsumed = 0;
    switch (mode) {
      case 0: // filter y when x fixed
        for (int i = 0; i < N; ++i) x[i]->attach(this, i, EVENT_F);
        y->attach(this, N, EVENT_F);
        break;
      case 1: // lb y
      default:
        for (int i = 0; i < N; i++) x[i]->attach(this, i, EVENT_LU);
        y->attach(this, N, EVENT_F);
        s->attach(this, N+1, EVENT_LU);
    }
  }
};

class GiniInt: public Propagator {
public:
  int const N;
  IntVar *y;
  vec<IntVar*> x;
  IntVar *s;
  int scale;
  int mode;

  vec<Tint> pos;

  Tint subsumed;
  Tint n_fixed;
  Tint all_fixed;
  Tint64_t glb;
  Tint64_t lub;
  vec<Tint> sortedbounds;
  Tint Mx;
  Tint hasM;

  bool setup;

  GiniInt(IntVar *_y, vec<IntVar*> &_x, IntVar *_s, int _scale, int _mode) :
  N(_x.size()), y(_y), x(_x), s(_s), scale(_scale), mode(_mode), setup(false) {
    for (int i = 0; i < N; ++i) {
      assert(x[i]->getMin() > 0);
    } assert(s->getMin() > 0);

    priority = 2;
    subsumed = 0;
    all_fixed = 0;
    hasM = 0;

    switch (mode) {
      case 0: // filter y when x fixed
        for (int i = 0; i < N; ++i) x[i]->attach(this, i, EVENT_F);
        y->attach(this, N, EVENT_F);
        break;
      default:
        // events
        for (int i = 0; i < N; i++) {
          x[i]->attach(this, i, EVENT_LU);
        }
        y->attach(this, N, EVENT_F);
        s->attach(this, N+1, EVENT_F);

        // trivial case
        if (mode == 9) {
          int64_t lub_ = INT64_MAX;
          int64_t glb_ = INT64_MIN;
          for (int i = 0; i < N; ++i) {
            if (x[i]->getMin() > glb_) glb_ = x[i]->getMin();
            if (x[i]->getMax() < lub_) lub_ = x[i]->getMax();
          }
          lub = lub_;
          glb = glb_;
        }

        // sorted bound end points
        int arr[2*N];
        for (int i = 0; i < 2*N; ++i) arr[i] = i;
        quickSort(arr, 0, 2*N-1);
        //for (int i = 1; i < 2*N; ++i) assert(valof(arr[i-1]) <= valof(arr[i]));
        //printf("%% OK\n");
        sortedbounds.growTo(2*N);
        for (int i = 0; i < 2*N; ++i) sortedbounds[i] = arr[i];

        // positions
        pos.growTo(N);
        for (int i = 0; i < N; ++i) pos[i] = 2;
    }

    int n_fixed_ = 0;
    for (int i = 0; i < N; ++i) {
      if (x[i]->isFixed()) n_fixed_++;
    }
    n_fixed = n_fixed_;
    if (n_fixed == N) {
      all_fixed = 1;
    }
    setup = true;
    pushInQueue();
  }

  int64_t valof(int i) {
    return i < N ? x[i]->getMin() : x[i-N]->getMax();
  }

  // A utility function to swap two elements
  void swap(int* a, int* b) {
    int t = *a;
    *a = *b;
    *b = t;
  }

  /* This function takes last element as pivot, places
     the pivot element at its correct position in sorted
     array, and places all smaller (smaller than pivot)
     to left of pivot and all greater elements to right
     of pivot */
  int partition (int arr[], int low, int high) {
    int64_t pivot = valof(arr[high]);    // pivot
    int i = (low - 1);  // Index of smaller element

    for (int j = low; j < high; j++) {
      // If current element is smaller than or
      // equal to pivot
      if (valof(arr[j]) <= pivot) {
        i++;    // increment index of smaller element
        swap(&arr[i], &arr[j]);
      }
    }
    swap(&arr[i + 1], &arr[high]);
    return (i + 1);
  }

  /* The main function that implements QuickSort
     arr[] --> Array to be sorted,
     low  --> Starting index,
     high  --> Ending index */
  void quickSort(int arr[], int low, int high) {
    if (low < high) {
      /* pi is partitioning index, arr[p] is now
         at right place */
      int pi = partition(arr, low, high);

      // Separately sort elements before
      // partition and after partition
      quickSort(arr, low, pi - 1);
      quickSort(arr, pi + 1, high);
    }
  }

  void wakeup(int i, int c) override {
    if (!setup) return;
    if (subsumed) return;

//    if (x[0]->getMin() <= 5757 && 5691 <= x[0]->getMax() &&
//        x[1]->getMin() <= 5772 && 5754 <= x[1]->getMax() &&
//        x[2]->getMin() <= 5758 && 5732 <= x[2]->getMax()) {
//      printf("%% SUPERKEY\n");
//    }

    if (mode == 9 && i < N) {
      int key, j;
      for(int i = 1; i<2*N; i++) {
        key = sortedbounds[i];//take value
        j = i;
        while(j > 0 && valof(sortedbounds[j-1])>valof(key)) {
          sortedbounds[j] = sortedbounds[j-1];
          j--;
        }
        sortedbounds[j] = key;   //insert in right place
      }
    }

    if (!all_fixed && i < N && c & EVENT_F) {
      n_fixed++;
      if (n_fixed == N) {
        all_fixed = 1;
//        for (int i = 0; i < N; ++i) {
//          assert(x[i]->isFixed() && "IS FIXED CALC WRONG"); // FIXME: REMOVE THIS BEFORE BENCHMARKS!!!
//        }
      }
    }

    if (mode == 9 && glb <= lub) { // Trivial case: Gini >= 0;
//      printf("%% TRIV CASE\n");
      if (i < N && c & EVENT_U && x[i]->getMax() < lub)
        lub = x[i]->getMax();
      if (i < N && c & EVENT_L && x[i]->getMin() > glb)
        glb = x[i]->getMin();
      if (glb > lub)
        pushInQueue(); // something of use can be done
      return;
    }

    if (!all_fixed && mode == 9 && i < N && hasM) {
//      printf("%% bounds case\n");
      int64_t xlb = x[i]->getMin();
      int64_t xub = x[i]->getMax();
      if (c & EVENT_U) {
        if (Mx <= xlb) return;
        else if (Mx <= xub) return;
        else pushInQueue();
      } else if (c & EVENT_L) {
        if (xub <= Mx) return;
        else if (xlb <= Mx) return;
        else pushInQueue();
      }
    }

    pushInQueue();
  }

  bool propagate() override {
    if (all_fixed) return prop_fix();
    else if (mode == 0) return true;
    else return prop_lb();
  }

  bool prop_lb() {
//    printf("%%PROP LB BEGIN-\n");

    int L = 0;
    int R = 2*N-1;
    int M = 0;
    int64_t G = 0;
    unsigned int seenL[N];
    unsigned int seenR[N];
    for (int i = 0; i < N; ++i) { seenL[i] = 0; seenR[i] = 0; }
    unsigned int seendicator = 0;
    int mid_L, mid_R;
    bool scan = false;
    while (L < R) {
      seendicator++;
      if (!scan) {
        mid_L = L + (R - L)/2;
        mid_R = mid_L + 1;
      } scan = false;

      int64_t dividend_L = 0, dividend_R = 0;
      int64_t divisor_L = 0, divisor_R = 0;
      int iR = 1;
      int iL = 1;
      for (int k = 0; k < 2*N; ++k) {
        int idx = sortedbounds[k];
        int idxN = idx < N ? idx : idx-N;
        int64_t point = valof(idx);
        int64_t nuL = valof(sortedbounds[mid_L]);
        int64_t nuR = valof(sortedbounds[mid_R]);
        if (idx < N) { // lower bound
          if (point < nuL) seenL[idxN] = seendicator; // lb below nuL
          else { // lb above/at nuL
            dividend_L += (2*(iL++) - N - 1) * point;
            divisor_L += N * point;
//            printf("    %% xi=%d ABOVE: dividend_L += %lli (= %lli)\n", idxN, (2*(iL-1) - N - 1) * point, dividend_L);
          }
          if (point < nuR) seenR[idxN] = seendicator; // lb below nuR
          else { // lb above/at nuR
            dividend_R += (2*(iR++) - N - 1) * point;
            divisor_R += N * point;
//            printf("    %% xi=%d ABOVE: dividend_R += %lli (= %lli)\n", idxN, (2*(iR-1) - N - 1) * point, dividend_R);
          }
        } else { // upper bound
          if (point < nuL) { // ub below nuL
            dividend_L += (2*(iL++) - N - 1) * point;
            divisor_L += N * point;
//            printf("    %% xi=%d BELOW: dividend_L += %lli (= %lli)\n", idxN, (2*(iL-1) - N - 1) * point, dividend_L);
          } else { // ub above/at mid_L
            if (seenL[idxN] == seendicator) {
              dividend_L += (2*(iL++) - N - 1) * nuL;
              divisor_L += N * nuL;
//              printf("    %% xi=%d OVERLAP: dividend_L += %lli (= %lli)\n", idxN, (2*(iL-1) - N - 1) * nuL, dividend_L);
            }
          }
          if (point < nuR) { // ub below nuR
            dividend_R += (2*(iR++) - N - 1) * point;
            divisor_R += N * point;
//            printf("    %% xi=%d BELOW: dividend_R += %lli (= %lli)\n", idxN, (2*(iR-1) - N - 1) * point, dividend_R);
          } else { // ub above/at nuR
            if (seenR[idxN] == seendicator) {
              dividend_R += (2*(iR++) - N - 1) * nuR;
              divisor_R += N * nuR;
//              printf("    %% xi=%d OVERLAP: dividend_R += %lli (= %lli)\n", idxN, (2*(iR-1) - N - 1) * nuR, dividend_R);
            }
          }
        }
      } //assert(iL == N+1 && iR == N+1);

//      printf("  %% divisor_L, divisor_R = %lli, %lli\n", divisor_L, divisor_R);

      const int reset = std::fegetround();
      std::fesetround(FE_DOWNWARD);
//      auto G_Lraw = ((long double) (dividend_L )) / (long double) divisor_L;
//      auto G_Rraw = ((long double) (dividend_R )) / (long double) divisor_R;
      auto G_L = (int64_t) (((long double) (dividend_L * scale)) / (long double) divisor_L);
      auto G_R = (int64_t) (((long double) (dividend_R * scale)) / (long double) divisor_R);
      std::fesetround(reset);

//      printf("  %% G_L, G_R = %lli, %lli\n", G_L, G_R);

//      printf("%% PRE LB Prop %%, (V_L at mid_L, V_R at mid_R) = (%lli at %lli, %lli at %lli)\n", V_L, mid_L, V_R, mid_R);
//      printf("  %% Sq_L=%lli, Sq_R=%lli, M_L=%lli, M_R=%lli\n", Sq_L, Sq_R, M_L, M_R);

      if (G_L == 0 || G_R == 0) {return true;} // worst lb found
      //if (G_L == V_R) {V = V_L; M = mid_L; break;} // found lb
      if      (G_L < G_R) {G = G_L; M = mid_L; R = mid_L;} // search left
      else if (G_L > G_R) {G = G_R; M = mid_R; L = mid_R;} // search right
      else { // G_L == G_R
        scan = true;
        if (L < mid_L) mid_L--;
        else if (mid_R < R) mid_R++;
        else {
          M = mid_L;
          G = G_L;
          break;
        }
        //printf("%% warning: G_L == G_R.\n");
        //assert(G_Lraw != G_Rraw);
        //return true;
      }
    }

    // update positions
    int64_t best_nu = valof(sortedbounds[M]);
    for (int i = 0; i < N; ++i) { // O(N)
      if      (best_nu < x[i]->getMin()) pos[i] =  1;
      else if (x[i]->getMax() < best_nu) pos[i] = -1;
      else                               pos[i] =  0;
    }
    hasM = 1;
    Mx = best_nu;

    // get scaled variance
    //const int reset = std::fegetround();
    //std::fesetround(FE_DOWNWARD);
    //auto scaled_var = (int64_t) (((long double) (V * scale)) / (N*N*N));
    //std::fesetround(reset);

//    printf("%% PRE LB Prop %%\n");
//    for (int i = 0; i < N; ++i) printf("   %% x[%d] = %d..%d      ", i, x[i]->getMin(), x[i]->getMax());
//    printf("%% y = %d..%d      ", y->getMin(), y->getMax());
//    printf("%% s = %d..%d\n", s->getMin(), s->getMax());
//    printf("   %% want to set y to %lli when it is %d..%d\n", G, y->getMin(), y->getMax());
//    printf("   %% nu idx = %d (pos %d), Mx (nu) = %d\n", sortedbounds[M].v, M, Mx.v);
//    printf("%% --->\n");
    if (y->setMinNotR(G)) {
      //n_prop_v_lb++;
      Clause* r = nullptr;
      if(so.lazy) {
        Lit lit[2*N+2];
        int lits = 0;
//        printf("constraint (");
        for(int ii = 0; ii < N; ++ii) {
          //if      (pos[ii] ==  1) {
          //  lit[lits++] = x[ii]->getMinLit();
//        //    printf("util[%d] >= %d /\\ ", ii+1, x[ii]->getMin());
          //}
          //else if (pos[ii] == -1) {
          //  lit[lits++] = x[ii]->getMaxLit();
//            printf("util[%d] <= %d /\\ ", ii+1, x[ii]->getMax());
          //}
          //else if (pos[ii] ==  0) {
          lit[lits++] = x[ii]->getMinLit();
          lit[lits++] = x[ii]->getMaxLit();
          //}
        }
//        if (M == s->getMin()) {
//          lit[lits++] = s->getMinLit();
//          printf("UTIL >= %d /\\ ", s->getMin());
//        }
//        if (M == s->getMax()) {
//          lit[lits++] = s->getMaxLit();
//          printf("UTIL <= %d /\\ ", s->getMax());
//        }

//        printf("true) -> (disp >= %d); %% EXPL\n", G);

        // lit[lits++] = y->getMinLit();
        // lit[lits++] = y->getMaxLit();
        r = Reason_new(lits+1);
        for(int ii = 0; ii < lits; ++ii) (*r)[ii+1] = lit[ii];
      }
//      if (scaled_var >= INT64_MAX)
//      printf("%% LB Prop %%\n");
//      for (int i = 0; i < N; ++i) printf("   %% x[%d] = %d..%d      ", i, x[i]->getMin(), x[i]->getMax());
//      printf("%% y = %d..%d      ", y->getMin(), y->getMax());
//      printf("%% s = %d..%d\n", s->getMin(), s->getMax());
//      printf("   %% want to set y to %lli when it is %d..%d\n", G, y->getMin(), y->getMax());
//      printf("   %% nu idx = %d (pos %d), Mx (nu) = %d\n", sortedbounds[M].v, M, Mx.v);
//      printf("%% <<<<---\n");
      if(!y->setMin(G, r)) {
        //n_incons_v_lb++;
        return false;
      }
    }
    return true;
  }

  bool prop_fix() {
    int64_t diff = 0;
    for (int i = 0; i < N; ++i) {
      for (int j = i+1; j < N; ++j) {
        diff += labs(x[i]->getVal() - x[j]->getVal());
      }
    } diff *= scale;

    int64_t sum = 0;
    // TODO: over-defensive
    if (s->isFixed()) sum = s->getVal();
    else {
      for (int i = 0; i < N; ++i) sum += x[i]->getVal();
    }

    Clause* r = nullptr;
    if(so.lazy) {
      // Set up reason
      r = Reason_new(N+1);
      for(int ii = 0; ii < N; ++ii) (*r)[ii+1] = x[ii]->getValLit();
    }

    const int reset = std::fegetround();
    std::fesetround(FE_DOWNWARD);
    auto gini_f = (long double) diff / (long double) (N * sum);
    int64_t gini = (int64_t) gini_f;
    std::fesetround(reset);

    // set y
    if(y->setValNotR(gini)) {
      if(!y->setVal(gini, r)) return false;
    }
    subsumed = 1;
    return true;
  }
};

class CovSq : public Propagator {
public:
	int const N;
	IntVar* y;
	vec<IntVar*> x;
	int scale;

	CovSq(IntVar* _y, vec<IntVar*>& _x, int _scale)	:
	  N(_x.size()), y(_y), x(_x), scale(_scale) {
    priority = 1;
		for (int i = 0; i < N; i++) x[i]->attach(this, i, EVENT_F);
		y->attach(this, N, EVENT_F);
	}

//	void wakeup(int i, int c) {
//		pushInQueue();
//	}

	bool propagate() {
    for (int i = 0; i < N; i++) {
      if (!x[i]->isFixed()) {
        return true;
      }
    }
//    printf("%% actual prop starting..\n");
    long double result_f;
		int64_t result = 0;
		int64_t dividend = 0;
	  int64_t divisor = 0;
    int64_t sumx = 0;
    for (int i = 0; i < N; i++) sumx += x[i]->getVal();
    divisor = N * sumx * sumx;
    for (int i = 0; i < N; i++) {
    	int64_t diff = N * x[i]->getVal() - sumx;
    	dividend += diff * diff;
    }
    result_f = (dividend * scale) / divisor;
    result = (int64_t) result_f;
//    printf("%% %lli / %lli = %Lf, then = %lld", dividend, divisor, result_f, result);
//    printf("%% %lld \n", result);
    if(y->setValNotR(result)) {
//      printf("%% setValNotR\n");
      Clause* r = nullptr;
      if(so.lazy) {
        // Set up reason
        r = Reason_new(N+1);
        for(int ii = 0; ii < N; ++ii) { (*r)[ii+1] = x[ii]->getValLit(); }
      }
      if(!y->setVal(result, r)) return false;
    }
    return true;
    //return y->setVal(result);
	}

//	void clearPropState() {
//		in_queue = false;
//	}
//
//	int checkSatisfied() {
//		return 1;
//	}

};

void covsq(IntVar* y, vec<IntVar*>& x, int scale) {
  new CovSq(y, x, scale);
}

void variance_int(IntVar* y, vec<IntVar*>& x, IntVar* s, int scale, int mode) {
  if (x.size() >= 1) new VarianceInt(y, x, s, scale, mode);
}

void gini_int(IntVar* y, vec<IntVar*>& x, IntVar* s, int scale, int mode) {
  if (x.size() >= 1) new GiniInt(y, x, s, scale, mode);
}
class SpreadFast : public Propagator {
public:
  int const N;
  int const vals;
  vec<IntVar *> x;
  vec<IntVar *> cl;
  IntVar *mean;
  IntVar *stdev;
  IntVar *median;
  int scale;

  Tint lb;
  Tint ub;

  SpreadFast(vec<IntVar *> &_x, vec<IntVar *> &_cl,
      IntVar *_mean, IntVar *_stdev, IntVar *_median,
      int _scale) :
  N(_x.size()), vals(_cl.size()), x(_x), cl(_cl),
  mean(_mean), stdev(_stdev), median(_median),
  scale(_scale) {
    priority = 1;
    int64_t _ub = INT64_MIN;
    int64_t _lb = INT64_MAX;
    for (int i = 0; i < N; ++i) {
      x[i]->attach(this, i, EVENT_F);
      if (x[i]->getMax() > _ub) _ub = x[i]->getMax();
      if (x[i]->getMin() < _lb) _lb = x[i]->getMin();
    }
    for (int i = 0; i < vals; ++i) cl[i]->attach(this, i, EVENT_F);
    mean->attach(this, N, EVENT_F);
    stdev->attach(this, N+1, EVENT_F);
    median->attach(this, N+2, EVENT_F);
    ub = _ub;
    lb = _lb;
  }

  bool propagate() {
    auto mean_ub_f = (long double) mean->getMax() / (long double) scale;
    auto mean_lb_f = (long double) mean->getMin() / (long double) scale;
    auto mua = (int64_t) ceil(mean_ub_f - lb);
    auto bmu = ub - (int64_t) mean_lb_f;





    return true;
  }

};

void spread_fast(vec<IntVar *> &x, vec<IntVar *> &cl,
    IntVar *mean, IntVar *stdev, IntVar *median,
    int scale) {
  new SpreadFast(x, cl, mean, stdev, median, scale);
}


class SpreadBounds : public Propagator {
public:
  int const N;
  vec<IntVar *> x;
  IntVar *mean;
  IntVar *stdev;
  IntVar *median;
  int scale;

  vec<Tint> _bounds;

  static int compare (const void * a, const void * b)
  {
    return ( *(int*)a - *(int*)b );
  }

  static void get_bounds (vec<Tint> *_bounds, vec< vec<int> > *bounds) {
    int len = _bounds->size();
    int arr[len][2];
    int act_len = 0;
    for (auto i = 0; i < len - 1; ++i) {
      if ((*_bounds)[i] != (*_bounds)[i+1]) {
        arr[i][0] = (*_bounds)[i];
        arr[i][1] = (*_bounds)[i+1];
        ++act_len;
      }
    }
    bounds->growTo(act_len);
//    printf("%% DAD, act_len = %d\n", act_len);
    for (auto i = 0; i < act_len; ++i) {
      (*bounds)[0].growTo(3);
      *bounds[i][0] = arr[i][0];
      *bounds[i][1] = arr[i][1];
//      printf("%% ss\n");
//      printf("%% %d = %d..%d\n", i, *bounds[i][0], *bounds[i][1]);
    }
  }

  SpreadBounds(vec<IntVar *> &_x,
      IntVar *_mean, IntVar *_stdev, IntVar *_median, int _scale) :
  N(_x.size()), x(_x),
  mean(_mean), stdev(_stdev), median(_median),
  scale(_scale) {
    priority = 1;
    _bounds.growTo(N*2);
    for (int i = 0; i < N; ++i) {
      x[i]->attach(this, i, EVENT_F);
      _bounds[i] = x[i]->getMin();
      _bounds[N+i] = x[i]->getMax();
    }
    mean->attach(this, N, EVENT_F);
    stdev->attach(this, N+1, EVENT_F);
    median->attach(this, N+2, EVENT_F);

    // sort bounds vector (but still dupes)
    qsort(&_bounds[0], _bounds.size(), sizeof(Tint), compare);

  }

  bool propagate() {
    qsort(&_bounds[0], _bounds.size(), sizeof(Tint), compare);
    vec< vec<int> > bounds;
    get_bounds(&_bounds, &bounds);

    int I = 0; // FIXME

    // optimal value
    // LI1
    // RI1
    // MI1
    // ESI1
    // q-opt and opt
    for (int k = 1; k < I; ++k) {
      //LIk
      //RIk
      //MIk
      //ESIk
      //VIk
      //GCIk
      // q-opt and opt
    }

    // bounds reduction

    return true;
  }
};

void spread_bounds(vec<IntVar *> &x,IntVar *mean, IntVar *stdev, IntVar *median,
                 int scale) {
  new SpreadBounds(x, mean, stdev, median, scale);
}