#include<iostream>

class C0 {
  public:
  virtual int m0() { return 0; }
  virtual int m1() { return 1; }
};

class C1 : public C0 {
  public:
  virtual int m0() { return 10; }
  virtual int m1() { return 11; }
};

int main() {
  C0 *c0 = new C0();
  C0 *c1 = new C1();
  std::cout << c0->m0() << std::endl;
  std::cout << c0->m1() << std::endl;
  std::cout << c1->m0() << std::endl;
  std::cout << c1->m1() << std::endl;
}
