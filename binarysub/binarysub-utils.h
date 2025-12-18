#ifndef BINARYSUB_UTILS_H
#define BINARYSUB_UTILS_H

#include <algorithm>
#include <memory>
#include <string>

namespace binarysub {

// Forward declaration for error handling
template <typename E> class unexpected {
public:
  explicit unexpected(const E &error) : error_(error) {}
  explicit unexpected(E &&error) : error_(std::move(error)) {}
  const E &error() const { return error_; }

private:
  E error_;
};

template <typename E>
unexpected<typename std::decay<E>::type> make_unexpected(E &&error) {
  return unexpected<typename std::decay<E>::type>(std::forward<E>(error));
}

template <typename T, typename E> class expected {
public:
  expected() : has_value_(true) { new (&value_) T(); }
  expected(const T &value) : has_value_(true) { new (&value_) T(value); }
  expected(T &&value) : has_value_(true) { new (&value_) T(std::move(value)); }

  template <typename U>
  expected(const unexpected<U> &error) : has_value_(false) {
    new (&error_) E(error.error());
  }

  ~expected() {
    if (has_value_) {
      value_.~T();
    } else {
      error_.~E();
    }
  }

  expected(const expected &other) : has_value_(other.has_value_) {
    if (has_value_) {
      new (&value_) T(other.value_);
    } else {
      new (&error_) E(other.error_);
    }
  }

  expected(expected &&other) : has_value_(other.has_value_) {
    if (has_value_) {
      new (&value_) T(std::move(other.value_));
    } else {
      new (&error_) E(std::move(other.error_));
    }
  }

  expected &operator=(const expected &other) {
    if (this != &other) {
      this->~expected();
      has_value_ = other.has_value_;
      if (has_value_) {
        new (&value_) T(other.value_);
      } else {
        new (&error_) E(other.error_);
      }
    }
    return *this;
  }

  expected &operator=(expected &&other) {
    if (this != &other) {
      this->~expected();
      has_value_ = other.has_value_;
      if (has_value_) {
        new (&value_) T(std::move(other.value_));
      } else {
        new (&error_) E(std::move(other.error_));
      }
    }
    return *this;
  }

  bool has_value() const { return has_value_; }
  operator bool() const { return has_value_; }
  bool operator!() const { return !has_value_; }

  const T &value() const { return value_; }
  T &value() { return value_; }

  const E &error() const { return error_; }

private:
  bool has_value_;
  union {
    T value_;
    E error_;
  };
};

// Specialization for void
template <typename E> class expected<void, E> {
public:
  expected() : has_value_(true) {}

  template <typename U>
  expected(const unexpected<U> &error)
      : has_value_(false), error_(error.error()) {}

  bool has_value() const { return has_value_; }
  operator bool() const { return has_value_; }
  bool operator!() const { return !has_value_; }

  const E &error() const { return error_; }

private:
  bool has_value_;
  E error_;
};

// ======================= Value-based shared_ptr wrapper ====================
// A shared_ptr wrapper that compares by value instead of by pointer
template <typename T> class value_ptr {
public:
  // Constructors
  value_ptr() : ptr_() {}
  value_ptr(std::nullptr_t) : ptr_(nullptr) {}
  explicit value_ptr(T *p) : ptr_(p) {}
  value_ptr(const std::shared_ptr<T> &p) : ptr_(p) {}
  value_ptr(std::shared_ptr<T> &&p) : ptr_(std::move(p)) {}

  // Default copy and move
  value_ptr(const value_ptr &) = default;
  value_ptr(value_ptr &&) = default;
  value_ptr &operator=(const value_ptr &) = default;
  value_ptr &operator=(value_ptr &&) = default;

  // shared_ptr interface
  T &operator*() const { return *ptr_; }
  T *operator->() const { return ptr_.get(); }
  T *get() const { return ptr_.get(); }
  explicit operator bool() const { return static_cast<bool>(ptr_); }

  void reset() { ptr_.reset(); }
  void reset(T *p) { ptr_.reset(p); }

  long use_count() const { return ptr_.use_count(); }
  bool unique() const { return ptr_.unique(); }

  // Access underlying shared_ptr
  const std::shared_ptr<T> &shared() const { return ptr_; }
  std::shared_ptr<T> &shared() { return ptr_; }

  // Value-based comparison operators
  friend bool operator==(const value_ptr &lhs, const value_ptr &rhs) {
    if (!lhs.ptr_ && !rhs.ptr_)
      return true;
    if (!lhs.ptr_ || !rhs.ptr_)
      return false;
    return *lhs.ptr_ == *rhs.ptr_;
  }

  friend bool operator!=(const value_ptr &lhs, const value_ptr &rhs) {
    return !(lhs == rhs);
  }

  friend bool operator<(const value_ptr &lhs, const value_ptr &rhs) {
    if (!lhs.ptr_ && !rhs.ptr_)
      return false;
    if (!lhs.ptr_)
      return true;
    if (!rhs.ptr_)
      return false;
    return *lhs.ptr_ < *rhs.ptr_;
  }

  friend bool operator<=(const value_ptr &lhs, const value_ptr &rhs) {
    return !(rhs < lhs);
  }

  friend bool operator>(const value_ptr &lhs, const value_ptr &rhs) {
    return rhs < lhs;
  }

  friend bool operator>=(const value_ptr &lhs, const value_ptr &rhs) {
    return !(lhs < rhs);
  }

  // Comparison with nullptr
  friend bool operator==(const value_ptr &lhs, std::nullptr_t) {
    return !lhs.ptr_;
  }

  friend bool operator==(std::nullptr_t, const value_ptr &rhs) {
    return !rhs.ptr_;
  }

  friend bool operator!=(const value_ptr &lhs, std::nullptr_t) {
    return static_cast<bool>(lhs.ptr_);
  }

  friend bool operator!=(std::nullptr_t, const value_ptr &rhs) {
    return static_cast<bool>(rhs.ptr_);
  }

private:
  std::shared_ptr<T> ptr_;
};

// Helper function to create value_ptr, similar to std::make_shared
template <typename T, typename... Args>
value_ptr<T> make_value_ptr(Args &&...args) {
  return value_ptr<T>(std::make_shared<T>(std::forward<Args>(args)...));
}

// ======================= Solver cache & error ==============================
struct Error {
  std::string msg;
  static Error make(std::string m);
};
inline Error Error::make(std::string m) { return {std::move(m)}; }

} // namespace binarysub

#endif
