// Authors: Daniel Ciołek, Antoni Maciąg

#ifndef JNP15_FUNCTION_MAXIMA_H
#define JNP15_FUNCTION_MAXIMA_H

#include <functional>
#include <set>
#include <cassert>
#include <memory>

class InvalidArg : public std::exception {
public:
    virtual const char* what () const throw ()
    {
        return "invalid argument value";
    }
};

template<typename A, typename V>
class FunctionMaxima{

public:

    class point_type{

        std::shared_ptr<A> argument;
        std::shared_ptr<V> val;

    private:

        point_type(const A& a, const  V& v)
        {
            argument = std::make_shared<A>(a);
            val = std::make_shared<V>(v);
        }

        friend class FunctionMaxima;

    public:

        A const& arg() const{
            return *argument;
        }

        V const& value() const{
            return *val;
        }

        point_type& operator=(const point_type &rhs){
            if(this == &rhs){
                return *this;
            }
            argument = rhs.argument;
            val = rhs.val;
            return *this;
        }

        point_type(const point_type& rhs):
        argument(rhs.argument),
        val(rhs.val)
        {}

    };


private:

    struct compare_points{

        using is_transparent = void;
        bool operator()(const point_type& lhs, const point_type& rhs) const {
            return lhs.arg() < rhs.arg();
        }

        bool operator()(const A& lhs, const point_type& rhs) const {
            return lhs < rhs.arg();
        }
        bool operator()(const point_type& lhs, const A& rhs) const {
            return lhs.arg() < rhs;
        }
    };

    struct compare_maxima{
        using is_transparent = void;
        bool operator()(const point_type& lhs, const point_type& rhs) const{
            if (rhs.value() < lhs.value()) return true;
            else if (lhs.value() < rhs.value()) return false;
            return lhs.arg() < rhs.arg();
        }
    };


public:
    using point_set = std::multiset<point_type, compare_points>;
    using iterator = typename point_set::const_iterator;

    using maxima_set = std::set<point_type, compare_maxima>;
    using mx_iterator = typename maxima_set::const_iterator;

private:

    point_set points;
    maxima_set maxima;

    // Sizes of buffers that are necessary for strong exception guarantee and
    // performing rollbacks of function operations.
    static const int NUMBER_TO_ERASE  = 5;
    static const int NUMBER_TO_ROLLBACK = 4;

    // Buffer necessary for strong exception guarantee in operations.
    mx_iterator to_erase[NUMBER_TO_ERASE];
    // Buffer necessary for performing rollbacks of function operations and.
    mx_iterator to_rollback[NUMBER_TO_ROLLBACK];
    bool if_erase[NUMBER_TO_ERASE];
    bool if_rollback[NUMBER_TO_ROLLBACK];

    // Resets the buffers to their default states.
    void clear_erase() {
        for(int i = 0; i < NUMBER_TO_ERASE; i++) {
            if_erase[i] = false;
        }
    }

    void clear_rollback() {
        for(int i = 0; i < NUMBER_TO_ROLLBACK; i++) {
            if_rollback[i] = false;
        }
    }

    // Rolling back the additions to the set of maxima.
    void rollback_maxima() {
        for(int i = 0; i < NUMBER_TO_ROLLBACK; i++) {
            if(if_rollback[i]) {
                maxima.erase(to_rollback[i]);
            }
        }
    }

    // No-throw.
    void erase_from_maxima() {
        for(int i = 0; i < NUMBER_TO_ERASE; i++) {
            if(if_erase[i]) {
                maxima.erase(to_erase[i]);
            }
        }
    }

    // In some of the functions below, to_be_erased is the iterator to a point_type that
    // is to be erased, either as a result of calling the 'erase' function or due to being
    // overwritten by a new value for its argument.

    // Returns the iterator to the point preceding p, skipping to_be_erased if necessary.
    iterator multi_prev(const iterator p, const iterator to_be_erased) const{
        return prev(p) == to_be_erased ? prev(prev(p)) : prev(p);
    }

    iterator multi_next(const iterator p, const iterator previous) const{
        if(p == points.end() || next(p) == points.end()) return points.end();
        return next(p) == previous ? next(next(p)) : next(p);
    }

    // Checks if p points to the first point of the function (or will point after
    // to_be erased is erased).
    bool multi_is_beginning(const iterator p, const iterator previous) const{
        if(p == points.begin()) return true;
        else if(prev(p) == previous && prev(p) == points.begin()) return true;
        return false;
    }

    bool multi_is_ending(const iterator p, const iterator previous) const{
        if(p == --points.end()) return true;
        else if(next(p) == previous && next(p) == --points.end()) return true;
        return false;
    }

    bool greater_than_next(const iterator p, const iterator previous) const{
        if(multi_is_ending(p, previous)) return true;
        if((*p).value() < (*(multi_next(p, previous))).value()) return false;
        return true;
    }

    bool greater_than_prev(const iterator p, const iterator previous) const{
        if(multi_is_beginning(p, previous)) return true;
        if((*p).value() < ((*(multi_prev(p, previous))).value())) return false;
        return true;
    }

    // This function has Strong Guarantee.
    bool is_maximum(const iterator p, const iterator previous) const {
        return greater_than_prev(p, previous) && greater_than_next(p, previous);
    }

    // This function has Strong Guarantee.
    bool present_in_maxima_set(const point_type& p){
        return maxima.find(p) != maxima.end();
    }

    // Checks if 'it' points to a point that is a local maximum, and adds/removes
    // it from the set of maxima accordingly. Strong Guarantee.
    void conditional_add_new_maximum(const iterator it, int i, const iterator previous) {
        if(it == points.end() || it == previous) return;
        bool is_max = is_maximum(it, previous);
        if (is_max) {
            if (!present_in_maxima_set(*it)) {
                to_rollback[i] = maxima.insert(*it).first;
                if_rollback[i] = true;
            }
        }
        else {
            if (present_in_maxima_set(*it)) {
                to_erase[i] = maxima.find(*it);
                if_erase[i] = true;
            }
        }
    }

    bool equivalent(V const& v1, V const& v2) const{
        if(v1 < v2) return false;
        if(v2 < v1) return false;
        return true;
    }

    // This function has Strong Guarantee.
    void custom_insert(A const& a, V const& v){

        iterator previous = points.find(a);
        if(previous != points.end() && equivalent(v, (*previous).value())) return;
        bool found = previous != points.end();
        iterator it = points.insert(point_type(a, v));

        try {

            conditional_add_new_maximum(it,1, previous);
            conditional_add_new_maximum(multi_next(it, previous), 2, previous);
            if(it != points.begin()) conditional_add_new_maximum(multi_prev(it, previous), 3, previous);
            if(found) {
                const point_type p = *previous;
                auto temp = maxima.find(p);
                if(temp != maxima.end()) {
                    to_erase[4] = temp;
                    if_erase[4] = true;
                }
                points.erase(previous);
            }

        }
        catch(...) {

            points.erase(it);
            rollback_maxima();
            clear_rollback();
            clear_erase();
            throw;

        }

        erase_from_maxima();
        clear_rollback();
        clear_erase();
    }

public:

    using size_type = size_t;

    void set_value(A const& a, V const& v){
        custom_insert(a, v);
    }

    iterator begin() const noexcept{
        return points.begin();
    }

    iterator end() const noexcept{
        return points.end();
    }

    iterator find(A const& a) const{
        return points.find(a);
    }

    mx_iterator mx_begin() const noexcept{
        return maxima.begin();
    }

    mx_iterator mx_end() const noexcept{
        return maxima.end();
    }

    void erase(A const& a){
        auto it = points.find(a);

        if(it != points.end()) {
            auto p = *it;

            auto it2 = maxima.find(p);
            try {
                if (it2 != maxima.end()) {
                    to_erase[0] = it2;
                    if_erase[0] = true;
                }
                conditional_add_new_maximum(next(it), 2, it);
                conditional_add_new_maximum(prev(it), 3, it);

            } catch (...) {
                rollback_maxima();

                clear_rollback();
                clear_erase();
                throw;
            }

            erase_from_maxima();
            points.erase(it);
            clear_rollback();
            clear_erase();
        }
    }

    // This function is no - throw.
    size_type size() const{
        return points.size();
    }

    // This function has Strong Guarantee.
    V const& value_at(A const& a) const {
        iterator res_it = points.find(a);
        if(res_it == points.end()) {
            throw InvalidArg();
        }
        V const& res = (*res_it).value();
        return res;
    }

    FunctionMaxima(): points(), maxima(), to_erase(), to_rollback(), if_erase(), if_rollback()
    {
        points = point_set();
        maxima = maxima_set();
        clear_erase();
        clear_rollback();
    }


    FunctionMaxima(const FunctionMaxima<A, V> & rhs):
    points(rhs.points),
    maxima(rhs.maxima),
    to_erase(),
    to_rollback(),
    if_erase(),
    if_rollback()
    {}

    void swap(FunctionMaxima& rhs) noexcept{
        std::swap(this->points, rhs.points);
        std::swap(this->maxima, rhs.maxima);
        std::swap(this->to_erase, rhs.to_erase);
        std::swap(this->to_rollback, rhs.to_rollback);
        std::swap(this->if_erase, rhs.if_erase);
        std::swap(this->if_rollback, rhs.if_rollback);
    }

    FunctionMaxima& operator=(const FunctionMaxima<A, V> &rhs){
        if(this == &rhs){
            return *this;
        }
        FunctionMaxima temp(rhs);
        temp.swap(*this);
        return *this;
    }

};

#endif //JNP15_FUNCTION_MAXIMA_H
