package target.exercise1;

import java.security.InvalidKeyException;
import java.security.NoSuchAlgorithmException;

import javax.crypto.BadPaddingException;
import javax.crypto.Cipher;
import javax.crypto.IllegalBlockSizeException;
import javax.crypto.KeyGenerator;
import javax.crypto.NoSuchPaddingException;
import javax.crypto.SecretKey;

public class NoMisuseHide {

	/**
	 * Misuse: "AES" is not secure, "AES/GCM/PKCS5Padding" should be used to get the cipher
	 */
	public void test() {
		try {
			String pt = "Sensitive information";
			int keySize = 128;
			// Generate a key for AES
			KeyGenerator kgen = KeyGenerator.getInstance("AES");
			kgen.init(keySize);
			SecretKey k = kgen.generateKey();
			// Encrypt the plain text with AES
			Cipher cp;
			String s = " Non sensitive information";
			pt += s;
			cp = Cipher.getInstance("AES/GCM/PKCS5Padding");
			cp.init(Cipher.ENCRYPT_MODE, k);
			byte[] encrypted= cp.doFinal(pt.getBytes());
		} catch (NoSuchAlgorithmException e) {
			e.printStackTrace();
		} catch (NoSuchPaddingException e) {
			e.printStackTrace();
		} catch (InvalidKeyException e) {
			e.printStackTrace();
		} catch (IllegalBlockSizeException e) {
			e.printStackTrace();
		} catch (BadPaddingException e) {
			e.printStackTrace();
		}
	}


}
