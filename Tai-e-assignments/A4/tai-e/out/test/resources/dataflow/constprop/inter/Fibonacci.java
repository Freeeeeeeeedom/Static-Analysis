public class Fibonacci {
    public static void main(String args[]) {
        int n = 5;
        int z = 0;
        z = getFibonacci(n);
    }

    public static int getFibonacci(int n) {
        if ((n == 0) || (n == 1)) {
            return n;
        } else {
            return getFibonacci(n - 1) + getFibonacci(n - 2);
        }
    }
}
