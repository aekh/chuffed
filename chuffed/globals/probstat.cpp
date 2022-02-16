#include <chuffed/core/propagator.h>
#include <stdlib.h>
#include <cfenv>

#include <iostream>
#include <fstream>

#include <stdio.h>
//#include <stdlib.h>

using namespace std;

using std::cout; using std::ofstream;
using std::endl; using std::string;

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

  bool daemon;
  bool trivlearn;

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
    if (mode == 10) {daemon = false; mode = 9;}
    else daemon = true;
    if (mode == 11) {trivlearn = true; mode = 9;}
    else trivlearn = false;
    switch (mode) {
      case 6:
        init_dc();
        break;
      case 9: // real version
        init_v1v2();
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
      if (n_fixed == N) {
        all_fixed = 1;
        pushInQueue();
        return;
      }
    }

    if (mode == 9 && glb <= lub && daemon) { // Trivial case: var >= 0;
      if (i < N && c & EVENT_U && x[i]->getMax() < lub)
        lub = x[i]->getMax();
      if (i < N && c & EVENT_L && x[i]->getMin() > glb)
        glb = x[i]->getMin();
      if (glb > lub)
        pushInQueue(); // something of use can be done
      return;
    }

    if (!all_fixed && mode == 9 && i < N && daemon) { // FIXME fix if run again
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
    if (all_fixed) return checking_prop();
    switch (mode) {
      case 6:
        return prop_x_dc();
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


  bool checking_prop() {
    // only propagate if all fixed
    if (!all_fixed) return true;

    // N*mean
    int64_t sumx = 0;
    for (int i = 0; i < N; i++) {
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
        Lit lit[2 * N + 2];
        int lits = 0;
        if (trivlearn) {
          for (int ii = 0; ii < N; ++ii) {
            lit[lits++] = x[ii]->getMinLit();
            lit[lits++] = x[ii]->getMaxLit();
          }
          lit[lits++] = s->getMinLit();
          lit[lits++] = s->getMaxLit();
        } else {
          for (int ii = 0; ii < N; ++ii) {
            if (pos[ii] == 1) {
              lit[lits++] = x[ii]->getMinLit();
            } else if (pos[ii] == -1) {
              lit[lits++] = x[ii]->getMaxLit();
            }
          }
          if (M == s->getMin()) {
            lit[lits++] = s->getMinLit();
          }
          if (M == s->getMax()) {
            lit[lits++] = s->getMaxLit();
          }
        }
        r = Reason_new(lits + 1);
        for (int ii = 0; ii < lits; ++ii) (*r)[ii + 1] = lit[ii];
      }
      if(!y->setMin(scaled_var, r)) {
        n_incons_v_lb++;
        return false;
      }
    }
    return true;
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

  bool daemon;
  bool trivlearn;

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

    if (mode == 10) {daemon = false; mode = 9;}
    else daemon = true;
    if (mode == 11) {trivlearn = true; mode = 9;}
    else trivlearn = false;
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
        pushInQueue();
        return;
      }
    }

    if (mode == 9 && glb <= lub && daemon) { // Trivial case: Gini >= 0;
      if (i < N && c & EVENT_U && x[i]->getMax() < lub)
        lub = x[i]->getMax();
      if (i < N && c & EVENT_L && x[i]->getMin() > glb)
        glb = x[i]->getMin();
      if (glb > lub)
        pushInQueue(); // something of use can be done
      return;
    }

    if (!all_fixed && mode == 9 && i < N && hasM && daemon) {
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
      if      (G_L < G_R) {G = G_L; M = mid_L; R = mid_L;} // search left
      else if (G_L > G_R) {G = G_R; M = mid_R; L = mid_R;} // search right
      else { // G_L == G_R
        if (L < mid_L) {scan = true; mid_L--;} // scan left
        else if (mid_R < R) {G = G_R; M = mid_R; L = mid_R;} // cut left
        else {M = mid_R; G = G_R; break;} // minimum found
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
        Lit lit[2*N];
        int lits = 0;
        if(trivlearn) {
          for(int ii = 0; ii < N; ++ii) {
            lit[lits++] = x[ii]->getMinLit();
            lit[lits++] = x[ii]->getMaxLit();
          }
        } else {
        printf("%% ---> LB Alg\n");
        printf("%%:%% constraint (");
          for(int ii = 0; ii < N; ++ii) {
            if (pos[ii] == 0) {
              if (x[ii]->getMin() == Mx.v) {
                lit[lits++] = x[ii]->getMinLit();
              printf("util[%d] >= %d /\\ ", ii+1, x[ii]->getMin());
              }
              if (x[ii]->getMax() == Mx.v) {
                lit[lits++] = x[ii]->getMaxLit();
              printf("util[%d] <= %d /\\ ", ii+1, x[ii]->getMax());
              }
            } else if (pos[ii] == 1) {
              lit[lits++] = x[ii]->getMinLit();
              printf("util[%d] >= %d /\\ ", ii+1, x[ii]->getMin());
            } else if (pos[ii] == -1) {
              lit[lits++] = x[ii]->getMaxLit();
              printf("util[%d] <= %d /\\ ", ii+1, x[ii]->getMax());
            }
            //else if (pos[ii] ==  0) {
            //lit[lits++] = x[ii]->getMinLit();
            //lit[lits++] = x[ii]->getMaxLit();
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

        printf("true) -> (disp >= %d); %% EXPL LB\n", G);

          // lit[lits++] = y->getMinLit();
          // lit[lits++] = y->getMaxLit();
        }
        r = Reason_new(lits+1);
        for(int ii = 0; ii < lits; ++ii) (*r)[ii+1] = lit[ii];
      }
//      if (scaled_var >= INT64_MAX)
      printf("%% LB Prop %%\n");
      for (int i = 0; i < N; ++i) printf("   %% x[%d] = %d..%d      ", i, x[i]->getMin(), x[i]->getMax());
      printf("%% y = %d..%d      ", y->getMin(), y->getMax());
      printf("%% s = %d..%d\n", s->getMin(), s->getMax());
      printf("   %% want to set y to %lli when it is %d..%d\n", G, y->getMin(), y->getMax());
      printf("   %% nu idx = %d (pos %d), Mx (nu) = %d\n", sortedbounds[M].v, M, Mx.v);
      printf("%% <<<<---\n");
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
      printf("%% =======> FIX Prop %%\n");
      printf("%%:%% constraint (");
      for(int ii = 0; ii < N; ++ii) {
        (*r)[ii+1] = x[ii]->getValLit();
        printf("util[%d] == %d /\\ ", ii+1, x[ii]->getValLit());
      }
    }

    const int reset = std::fegetround();
    std::fesetround(FE_DOWNWARD);
    auto gini_f = (long double) diff / (long double) (N * sum);
    int64_t gini = (int64_t) gini_f;
    std::fesetround(reset);

    printf("true) -> (disp == %d); %% EXPL FIX\n", gini);

    for (int i = 0; i < N; ++i) printf("   %% x[%d] = %d..%d      ", i, x[i]->getMin(), x[i]->getMax());
    printf("%% y = %d..%d      ", y->getMin(), y->getMax());
    printf("%% s = %d..%d\n", s->getMin(), s->getMax());
    printf("   %% want to set y to %lli when it is %d..%d\n", gini, y->getMin(), y->getMax());
    //printf("   %% nu idx = %d (pos %d), Mx (nu) = %d\n", sortedbounds[M].v, M, Mx.v);
    printf("%% <<<<---\n");

    // set y
    if(y->setValNotR(gini)) {
      if(!y->setVal(gini, r)) return false;
    }
    subsumed = 1;
    return true;
  }
};

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