#include "function_maxima.h"

#include <cassert>
#include <iostream>
#include <vector>

class Secret {
public:
  int get() const {
    return value;
  }
  bool operator<(const Secret &a) const {
    return value < a.value;
  }
  static Secret create(int v) {
    return Secret(v);
  }
private:
  Secret(int v) : value(v) {
  }
  int value;
};

template<typename A, typename V>
struct same {
  bool operator()(const typename FunctionMaxima<A, V>::point_type &p,
                  const std::pair<A, V> &q) {
    return !(p.arg() < q.first) && !(q.first < p.arg()) &&
           !(p.value() < q.second) && !(q.second < p.value());
  }
};

template<typename A, typename V>
bool fun_equal(const FunctionMaxima<A, V> &F,
               const std::initializer_list<std::pair<A, V>> &L) {
  return F.size() == L.size() &&
         std::equal(F.begin(), F.end(), L.begin(), same<A, V>());
}

template<typename A, typename V>
bool fun_mx_equal(const FunctionMaxima<A, V> &F,
                  const std::initializer_list<std::pair<A, V>> &L) {
  return static_cast<typename FunctionMaxima<A, V>::size_type>(std::distance(F.mx_begin(), F.mx_end())) == L.size() &&
         std::equal(F.mx_begin(), F.mx_end(), L.begin(), same<A, V>());
}

int main() {
  FunctionMaxima<int, int> fun;
  fun.set_value(0, 1);
  assert(fun_equal(fun, {{0, 1}}));
  assert(fun_mx_equal(fun, {{0, 1}}));

  fun.set_value(0, 0);
  assert(fun_equal(fun, {{0, 0}}));
  assert(fun_mx_equal(fun, {{0, 0}}));

  fun.set_value(1, 0);
  fun.set_value(2, 0);
  assert(fun_equal(fun, {{0, 0}, {1, 0}, {2, 0}}));
  assert(fun_mx_equal(fun, {{0, 0}, {1, 0}, {2, 0}}));

  fun.set_value(1, 1);
  assert(fun_mx_equal(fun, {{1, 1}}));

  fun.set_value(2, 2);
  assert(fun_mx_equal(fun, {{2, 2}}));
  fun.set_value(0, 2);
  fun.set_value(1, 3);
  assert(fun_mx_equal(fun, {{1, 3}}));

  try {
    std::cout << fun.value_at(4) << std::endl;
    assert(false);
  } catch (InvalidArg &e) {
    std::cout << e.what() << std::endl;
  }

  fun.erase(1);
  assert(fun.find(1) == fun.end());
  assert(fun_mx_equal(fun, {{0, 2}, {2, 2}}));

  fun.set_value(-2, 0);
  fun.set_value(-1, -1);
  assert(fun_mx_equal(fun, {{0, 2}, {2, 2}, {-2, 0}}));

  std::vector<FunctionMaxima<Secret, Secret>::point_type> v;
  {
    FunctionMaxima<Secret, Secret> temp;
    temp.set_value(Secret::create(1), Secret::create(10));
    temp.set_value(Secret::create(2), Secret::create(20));
    v.push_back(*temp.begin());
    v.push_back(*temp.mx_begin());
  }
  assert(v[0].arg().get() == 1);
  assert(v[0].value().get() == 10);
  assert(v[1].arg().get() == 2);
  assert(v[1].value().get() == 20);

  // To powinno działać szybko.
  FunctionMaxima<int, int> big;
  using size_type = decltype(big)::size_type;
  const size_type N = 100000;
  for (size_type i = 1; i <= N; ++i) {
    big.set_value(i, i);
  }
  size_type counter = 0;
  for (size_type i = 1; i <= N; ++i) {
    big.set_value(i, big.value_at(i) + 1);
    for (auto it = big.mx_begin(); it != big.mx_end(); ++it) {
      ++counter;
    }
  }
  assert(counter == 2 * N - 1);
  big = fun;
}
