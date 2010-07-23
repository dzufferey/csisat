public class CSIsatWrap {

    static {
	System.loadLibrary("csisat_wrap");
    }

    public static native String interpolateString(String s);

    public static void main(String[] args) {
	System.out.println(CSIsatWrap.interpolateString("blablabla"));
    }

}
