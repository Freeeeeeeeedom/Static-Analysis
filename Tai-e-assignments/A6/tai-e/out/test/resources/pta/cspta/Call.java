public class Call {

    public static void main(String[] args) {
        A a = new A();
        B b = new B();
        C c = new C();
        C x = a.foo(b, c);
    }
}

class A {

    C foo(B b, C c) {
        return c;
    }
}

class B {
}

class C {
}
