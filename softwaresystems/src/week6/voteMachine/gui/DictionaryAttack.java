package week6.voteMachine.gui;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.HashMap;
import java.util.Map;

import org.apache.commons.codec.binary.Hex;

public class DictionaryAttack {
	private Map<String, String> passwordMap;
	private Map<String, String> hashDictionary;

	public DictionaryAttack() {
		hashDictionary = new HashMap<String, String>();
	}

	/**
	 * Reads a password file. Each line of the password file has the form:
	 * username: encodedpassword
	 * 
	 * After calling this method, the passwordMap class variable should be
	 * filled withthe content of the file. The key for the map should be the
	 * username, and the password hash should be the content.
	 * 
	 * @param filename
	 * @throws IOException
	 * @throws FileNotFoundException
	 */
	public void readPasswords(String filename) throws FileNotFoundException, IOException {
		passwordMap = new HashMap<String, String>();

		try (FileReader reader = new FileReader(filename)) {
			try (BufferedReader bufferedReader = new BufferedReader(reader)) {
				String currentLine;
				while ((currentLine = bufferedReader.readLine()) != null) {
					String[] parts = currentLine.split(": ");
					passwordMap.put(parts[0], parts[1]);
				}
			}
		}
	}

	/**
	 * Given a password, return the MD5 hash of a password. The resulting hash
	 * (or sometimes called digest) should be hex-encoded in a String.
	 * 
	 * @param password
	 * @return
	 */
	public String getPasswordHash(String password) {
		String result = null;
		try {
			MessageDigest digest = MessageDigest.getInstance("MD5");
			digest.update(password.getBytes());
			result = Hex.encodeHexString(digest.digest());
		} catch (NoSuchAlgorithmException e) {
			// MD5 algorithm could not be found.
		}
		return result;
	}

	/**
	 * Checks the password for the user the password list. If the user does not
	 * exist, returns false.
	 * 
	 * @param user
	 * @param password
	 * @return whether the password for that user was correct.
	 */
	public boolean checkPassword(String user, String password) {
		return passwordMap.containsKey(user) && passwordMap.get(user).equals(getPasswordHash(password));
	}

	/**
	 * Reads a dictionary from file (one line per word) and use it to add
	 * entries to a dictionary that maps password hashes (hex-encoded) to the
	 * original password.
	 * 
	 * @param filename
	 *            filename of the dictionary.
	 * @throws IOException
	 * @throws FileNotFoundException
	 */
	public void addToHashDictionary(String filename) throws FileNotFoundException, IOException {
		try (FileReader reader = new FileReader(filename)) {
			try (BufferedReader bufferedReader = new BufferedReader(reader)) {
				String currentLine;
				while ((currentLine = bufferedReader.readLine()) != null) {
					hashDictionary.put(getPasswordHash(currentLine), currentLine);
				}
			}
		}
	}

	/**
	 * Do the dictionary attack.
	 */
	public void doDictionaryAttack() {

		int passwordsCracked = 0;

		System.out.println("  Username | Password ");
		System.out.println("-----------+-----------------");

		for (Map.Entry<String, String> nameHashEntry : passwordMap.entrySet()) {
			String name = nameHashEntry.getKey();
			String passwordHash = nameHashEntry.getValue();

			if (hashDictionary.containsKey(passwordHash)) {
				System.out.println(String.format("%10s | %-10s", name, hashDictionary.get(passwordHash)));
				passwordsCracked++;
			}
		}

		System.out.println(String.format("%d of %d passwords found.", passwordsCracked, passwordMap.size()));
	}

	public static void main(String[] args) {
		DictionaryAttack da = new DictionaryAttack();

		try {
			da.readPasswords("C:\\Users\\Gebruiker\\Documents\\School\\Technische Informatica\\SSHome\\workspace\\softwaresystems\\bin\\ss\\week6\\test\\LeakedPasswords.txt");
			da.addToHashDictionary("C:\\users\\gebruiker\\desktop\\most used passwords.txt");
			da.addToHashDictionary("C:\\users\\gebruiker\\desktop\\linuxwords");
			da.doDictionaryAttack();
		} catch (FileNotFoundException e) {
			System.out.println("Could not find one of the required files.");
		} catch (IOException e) {
			System.out.println("Could not read one of the required files.");
		}
	}

}