import language from "../language/LanguageBeta";
import backend from "../backend/BackendB";
import frontend from "../frontend/Frontend2";

export default function editor() { return frontend(backend(language())) }