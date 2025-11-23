package analysis;

import java.util.HashSet;
import java.util.Set;
import javax.annotation.Nonnull;
import sootup.core.jimple.basic.Value;

/**
 * The Class FileStateFact records the state of a file object
 */
public class FileStateFact{

	public enum FileState {
		Init, Open, Close
	}
	
	/** The aliases point to the same File object. */
	private final Set<Value> aliases;

	/** The state of the file object.*/
	private FileState state;

	public FileStateFact(@Nonnull FileStateFact fsf) {
		this(new HashSet<>(fsf.aliases),fsf.state);
	}

	public FileStateFact(@Nonnull FileState state) {
		this(new HashSet<>(), state);
	}

	public FileStateFact(@Nonnull Set<Value> aliases, @Nonnull FileState state) {
		this.aliases = aliases;
		this.state = state;
	}

	public void updateState(@Nonnull FileState state) {
		this.state = state;
	}

	public void addAlias(@Nonnull Value alias) {
		this.aliases.add(alias);
	}

	public boolean isOpened() {
		return state == FileState.Open;
	}

	public boolean containsAlias(@Nonnull Value value) {
		for (Value alias : aliases) {
			if (alias.equivTo(value)) {
				return true;
			}
		}
		return false;
	}

	public boolean containsAlias(@Nonnull String value) {
		for (Value alias : aliases) {
			if (alias.toString().equals(value)) {
                return true;
            }
		}
		return false;
	}

	@Nonnull
	public FileState getState() {
		return this.state;
	}

	@Override
	@Nonnull
	public String toString() {
		return "(" + aliases + ", " + state + ")";
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + aliases.hashCode();
		result = prime * result + ((state == null) ? 0 : state.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
            return true;
        }
		if (obj == null) {
            return false;
        }
		if (getClass() != obj.getClass()) {
            return false;
        }
		FileStateFact other = (FileStateFact) obj;
        if (!aliases.equals(other.aliases)) {
            return false;
        }
        return state == other.state;
    }


}
